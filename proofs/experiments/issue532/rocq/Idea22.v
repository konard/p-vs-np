(* Issue #532, Idea 22: decision-to-search self-reduction for SAT.

   Rocq counterpart of lean/Idea22.lean.  For every decision procedure dec
   with Decides dec, the search that fixes the variables of vs one at a time
   returns a satisfying assignment of every satisfiable CNF whose variables
   lie in vs (search_correct), asks exactly length vs questions
   (search_calls), and costs at most length vs times a polynomial bound on
   the questions (searchCost_le, searchCost_le_measure).  The schema
   ExactPolyDeciderFor (relative to an abstract cost model) yields
   PolySearchFor (decision_to_search_for); it is trivial in the zero cost
   model (zero_cost_trivial).  In the shared machine model the open
   obligation ExactPolyDecider (PolyDec SAT) yields PolySearch, a machine
   whose answers drive the self-reduction with total Run step count
   polynomial in the encoding length (decision_to_search); with SATHard it
   gives P = NP (pEqualsNP_of_exactPolyDecider).  A correct search yields a
   decider (search_gives_decider) and an exponential exact decider exists
   unconditionally (satDec_correct).
   Rocq difference from Lean: machineDec and runTime are clocked by an
   explicit polynomial (computed with runFor / timeFor) instead of being
   chosen classically, so PolySearch uses the same polynomial p for the
   halting bound and for the clock.
   Verdict: correct tool, insufficient alone. *)

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

(* ---------- Restriction ---------- *)

Fixpoint clauseHas (v : nat) (b : bool) (C : Clause) : bool :=
  match C with
  | [] => false
  | l :: C' => (Nat.eqb (var l) v && Bool.eqb (pos l) b) || clauseHas v b C'
  end.

Fixpoint removeVar (v : nat) (C : Clause) : Clause :=
  match C with
  | [] => []
  | l :: C' => if Nat.eqb (var l) v then removeVar v C' else l :: removeVar v C'
  end.

Fixpoint restrict (v : nat) (b : bool) (phi : CNF) : CNF :=
  match phi with
  | [] => []
  | C :: phi' =>
      if clauseHas v b C then restrict v b phi' else removeVar v C :: restrict v b phi'
  end.

Definition setVar (a : Assignment) (v : nat) (b : bool) : Assignment :=
  fun x => if Nat.eqb x v then b else a x.

Lemma evalClause_setVar : forall a v b C,
  evalClause (setVar a v b) C = clauseHas v b C || evalClause a (removeVar v C).
Proof.
  intros a v b C. induction C as [|l C IH]; [reflexivity|].
  cbn [evalClause clauseHas removeVar]. rewrite IH.
  destruct (Nat.eqb (var l) v) eqn:E.
  - cbn [andb].
    generalize (clauseHas v b C) as x. generalize (evalClause a (removeVar v C)) as y.
    intros y x. apply Nat.eqb_eq in E. unfold evalLit, setVar. rewrite E, Nat.eqb_refl.
    destruct (pos l), b, x, y; reflexivity.
  - cbn [andb orb evalClause].
    generalize (clauseHas v b C) as x. generalize (evalClause a (removeVar v C)) as y.
    intros y x. unfold evalLit, setVar. rewrite E.
    destruct (pos l), (a (var l)), x, y; reflexivity.
Qed.

Theorem eval_restrict : forall a v b phi,
  evalCNF a (restrict v b phi) = evalCNF (setVar a v b) phi.
Proof.
  intros a v b phi. induction phi as [|C phi IH]; [reflexivity|].
  cbn [evalCNF restrict]. rewrite evalClause_setVar.
  destruct (clauseHas v b C); cbn [evalCNF orb andb]; rewrite IH; reflexivity.
Qed.

Lemma evalClause_congr : forall a a' C,
  (forall l, In l C -> a (var l) = a' (var l)) -> evalClause a C = evalClause a' C.
Proof.
  intros a a' C H. induction C as [|l C IH]; [reflexivity|].
  cbn [evalClause]. rewrite IH by (intros l' Hl'; apply H; right; exact Hl').
  unfold evalLit. rewrite (H l (or_introl eq_refl)). reflexivity.
Qed.

Theorem eval_congr : forall a a' phi,
  (forall C l, In C phi -> In l C -> a (var l) = a' (var l)) ->
  evalCNF a phi = evalCNF a' phi.
Proof.
  intros a a' phi H. induction phi as [|C phi IH]; [reflexivity|].
  cbn [evalCNF]. rewrite IH by (intros C' l HC' Hl; apply (H C'); [right|]; auto).
  rewrite (evalClause_congr a a' C) by (intros l Hl; apply (H C); [left|]; auto).
  reflexivity.
Qed.

Lemma setVar_self : forall a v x, setVar a v (a v) x = a x.
Proof.
  intros a v x. unfold setVar. destruct (Nat.eqb x v) eqn:E; [|reflexivity].
  apply Nat.eqb_eq in E. subst. reflexivity.
Qed.

Theorem sat_split : forall phi v,
  Satisfiable phi <-> Satisfiable (restrict v true phi) \/ Satisfiable (restrict v false phi).
Proof.
  intros phi v. split.
  - intros [a Ha].
    assert (Hr : evalCNF a (restrict v (a v) phi) = true).
    { rewrite eval_restrict. rewrite (eval_congr _ a); auto.
      intros C l _ _. apply setVar_self. }
    destruct (a v); [left|right]; exists a; exact Hr.
  - intros [[a Ha]|[a Ha]].
    + exists (setVar a v true). rewrite <- eval_restrict. exact Ha.
    + exists (setVar a v false). rewrite <- eval_restrict. exact Ha.
Qed.

(* ---------- Occurring variables ---------- *)

Definition VarsIn (phi : CNF) (vs : list nat) : Prop :=
  forall C l, In C phi -> In l C -> In (var l) vs.

Lemma mem_removeVar : forall v C l, In l (removeVar v C) -> In l C /\ var l <> v.
Proof.
  intros v C l. induction C as [|l' C IH]; cbn [removeVar]; [intros []|].
  destruct (Nat.eqb (var l') v) eqn:E.
  - intros H. destruct (IH H). split; [right|]; auto.
  - intros [H|H].
    + subst. split; [left; reflexivity|]. apply Nat.eqb_neq. exact E.
    + destruct (IH H). split; [right|]; auto.
Qed.

Lemma mem_restrict : forall v b phi C',
  In C' (restrict v b phi) -> exists C, In C phi /\ C' = removeVar v C.
Proof.
  intros v b phi C'. induction phi as [|C phi IH]; cbn [restrict]; [intros []|].
  destruct (clauseHas v b C).
  - intros H. destruct (IH H) as [D [HD E]]. exists D. split; [right|]; auto.
  - intros [H|H].
    + exists C. split; [left|]; auto.
    + destruct (IH H) as [D [HD E]]. exists D. split; [right|]; auto.
Qed.

Theorem restrict_vars : forall phi v vs b,
  VarsIn phi (v :: vs) -> VarsIn (restrict v b phi) vs.
Proof.
  intros phi v vs b H C' l HC' Hl.
  destruct (mem_restrict v b phi C' HC') as [C [HC E]]. subst C'.
  destruct (mem_removeVar v C l Hl) as [HlC Hne].
  destruct (H C l HC HlC) as [E|E]; [congruence | exact E].
Qed.

Theorem sat_no_vars : forall phi, VarsIn phi [] ->
  (Satisfiable phi <-> evalCNF (fun _ => false) phi = true).
Proof.
  intros phi H. split.
  - intros [a Ha]. rewrite (eval_congr _ a); auto.
    intros C l HC Hl. destruct (H C l HC Hl).
  - intros H'. exists (fun _ => false). exact H'.
Qed.

Fixpoint solve (vs : list nat) (phi : CNF) : bool :=
  match vs with
  | [] => evalCNF (fun _ => false) phi
  | v :: vs' => solve vs' (restrict v true phi) || solve vs' (restrict v false phi)
  end.

Theorem solve_correct : forall vs phi, VarsIn phi vs ->
  (solve vs phi = true <-> Satisfiable phi).
Proof.
  induction vs as [|v vs IH]; intros phi H.
  - cbn [solve]. rewrite sat_no_vars by exact H. reflexivity.
  - cbn [solve]. rewrite sat_split with (v := v), orb_true_iff.
    rewrite (IH _ (restrict_vars phi v vs true H)), (IH _ (restrict_vars phi v vs false H)).
    reflexivity.
Qed.

(* ---------- Size and variables ---------- *)

Fixpoint size (phi : CNF) : nat :=
  match phi with
  | [] => 0
  | C :: phi' => length C + 1 + size phi'
  end.

Lemma length_removeVar_le : forall v C, length (removeVar v C) <= length C.
Proof.
  intros v C. induction C as [|l C IH]; cbn [removeVar length]; [lia|].
  destruct (Nat.eqb (var l) v); cbn [length]; lia.
Qed.

Theorem size_restrict_le : forall v b phi, size (restrict v b phi) <= size phi.
Proof.
  intros v b phi. induction phi as [|C phi IH]; cbn [restrict size]; [lia|].
  pose proof (length_removeVar_le v C).
  destruct (clauseHas v b C); cbn [size]; lia.
Qed.

Fixpoint varsOf (phi : CNF) : list nat :=
  match phi with
  | [] => []
  | C :: phi' => map var C ++ varsOf phi'
  end.

Theorem varsOf_spec : forall phi, VarsIn phi (varsOf phi).
Proof.
  intros phi. induction phi as [|D phi IH]; intros C l HC Hl; [destruct HC|].
  cbn [varsOf]. apply in_or_app. destruct HC as [E|E].
  - subst D. left. apply in_map. exact Hl.
  - right. exact (IH C l E Hl).
Qed.

Theorem varsOf_length_le : forall phi, length (varsOf phi) <= size phi.
Proof.
  intros phi. induction phi as [|C phi IH]; cbn [varsOf size length]; [lia|].
  rewrite length_app, length_map. lia.
Qed.

(* ---------- Deciders and the self-reduction ---------- *)

Definition Decides (dec : CNF -> bool) : Prop :=
  forall psi, dec psi = true <-> Satisfiable psi.

Fixpoint search (dec : CNF -> bool) (vs : list nat) (phi : CNF) : Assignment * nat :=
  match vs with
  | [] => ((fun _ => false), 0)
  | v :: vs' =>
      let b := dec (restrict v true phi) in
      let r := search dec vs' (restrict v b phi) in
      (setVar (fst r) v b, S (snd r))
  end.

Theorem search_correct : forall dec, Decides dec -> forall vs phi,
  VarsIn phi vs -> Satisfiable phi -> evalCNF (fst (search dec vs phi)) phi = true.
Proof.
  intros dec Hdec vs. induction vs as [|v vs IH]; intros phi Hv Hs.
  - cbn [search fst]. apply (sat_no_vars phi Hv). exact Hs.
  - assert (Hb : Satisfiable (restrict v (dec (restrict v true phi)) phi)).
    { destruct (dec (restrict v true phi)) eqn:E.
      - apply Hdec. exact E.
      - assert (Hn : ~ Satisfiable (restrict v true phi)).
        { intros Hsat. apply Hdec in Hsat. congruence. }
        destruct (proj1 (sat_split phi v) Hs) as [H1|H2]; [contradiction|exact H2]. }
    cbn [search fst]. rewrite <- eval_restrict.
    apply IH; [apply restrict_vars; exact Hv | exact Hb].
Qed.

Theorem search_calls : forall dec vs phi, snd (search dec vs phi) = length vs.
Proof.
  intros dec vs. induction vs as [|v vs IH]; intros phi; [reflexivity|].
  cbn [search snd length]. rewrite IH. reflexivity.
Qed.

Theorem search_decides : forall dec, Decides dec -> forall vs phi, VarsIn phi vs ->
  (evalCNF (fst (search dec vs phi)) phi = true <-> Satisfiable phi).
Proof.
  intros dec Hdec vs phi Hv. split.
  - intros H. exists (fst (search dec vs phi)). exact H.
  - apply search_correct; assumption.
Qed.

Definition fullSearch (dec : CNF -> bool) (phi : CNF) : Assignment * nat :=
  search dec (varsOf phi) phi.

Theorem fullSearch_correct : forall dec, Decides dec -> forall phi,
  Satisfiable phi -> evalCNF (fst (fullSearch dec phi)) phi = true.
Proof.
  intros dec Hdec phi Hs. apply search_correct; [exact Hdec | apply varsOf_spec | exact Hs].
Qed.

Theorem fullSearch_calls_le : forall dec phi, snd (fullSearch dec phi) <= size phi.
Proof.
  intros dec phi. unfold fullSearch. rewrite search_calls. apply varsOf_length_le.
Qed.

Theorem search_gives_decider : forall S : CNF -> Assignment,
  (forall phi, Satisfiable phi -> evalCNF (S phi) phi = true) ->
  Decides (fun phi => evalCNF (S phi) phi).
Proof.
  intros S HS phi. split.
  - intros H. exists (S phi). exact H.
  - apply HS.
Qed.

(* ---------- Costs ---------- *)

Definition polyEval (c k n : nat) : nat := c * (n + 1) ^ k.

Lemma polyEval_mono : forall c k m n, m <= n -> polyEval c k m <= polyEval c k n.
Proof.
  intros c k m n H. unfold polyEval. apply Nat.mul_le_mono_l.
  apply Nat.pow_le_mono_l. lia.
Qed.

Lemma mul_polyEval_le : forall c k n, n * polyEval c k n <= polyEval c (k + 1) n.
Proof.
  intros c k n. unfold polyEval. rewrite Nat.pow_add_r, Nat.pow_1_r.
  replace (n * (c * (n + 1) ^ k)) with (c * (n + 1) ^ k * n) by ring.
  rewrite Nat.mul_assoc. apply Nat.mul_le_mono_l. lia.
Qed.

Fixpoint searchCost (dec : CNF -> bool) (cost : CNF -> nat) (vs : list nat) (phi : CNF) : nat :=
  match vs with
  | [] => 0
  | v :: vs' =>
      cost (restrict v true phi)
      + searchCost dec cost vs' (restrict v (dec (restrict v true phi)) phi)
  end.

Theorem searchCost_le : forall dec cost c k,
  (forall psi, cost psi <= polyEval c k (size psi)) ->
  forall vs phi, searchCost dec cost vs phi <= length vs * polyEval c k (size phi).
Proof.
  intros dec cost c k Hc vs. induction vs as [|v vs IH]; intros phi; [cbn; lia|].
  cbn [searchCost length].
  pose proof (Nat.le_trans _ _ _ (Hc (restrict v true phi))
    (polyEval_mono c k _ _ (size_restrict_le v true phi))) as H1.
  pose proof (Nat.le_trans _ _ _ (IH (restrict v (dec (restrict v true phi)) phi))
    (Nat.mul_le_mono_l _ _ (length vs)
      (polyEval_mono c k _ _ (size_restrict_le v (dec (restrict v true phi)) phi)))) as H2.
  lia.
Qed.

(** Cost of the self-reduction for any size measure: if restriction does not
    increase the measure [mu] and each question costs at most [B (mu psi)]
    for a monotone [B], the whole search costs at most
    [length vs * B (mu phi)]. *)
Theorem searchCost_le_measure : forall (dec : CNF -> bool) (cost : CNF -> nat)
    (mu : CNF -> nat) (B : nat -> nat),
  (forall m n, m <= n -> B m <= B n) ->
  (forall v b psi, mu (restrict v b psi) <= mu psi) ->
  (forall psi, cost psi <= B (mu psi)) ->
  forall vs phi, searchCost dec cost vs phi <= length vs * B (mu phi).
Proof.
  intros dec cost mu B hB hmu hc vs. induction vs as [|v vs IH]; intros phi; [cbn; lia|].
  cbn [searchCost length].
  pose proof (Nat.le_trans _ _ _ (hc (restrict v true phi)) (hB _ _ (hmu v true phi))) as H1.
  pose proof (Nat.le_trans _ _ _ (IH (restrict v (dec (restrict v true phi)) phi))
    (Nat.mul_le_mono_l _ _ (length vs) (hB _ _ (hmu v (dec (restrict v true phi)) phi))))
    as H2.
  lia.
Qed.

(** A cost model for the schema below: a cost for running a decider on an
    input.  The schema is only as meaningful as the cost model it is
    instantiated with (in the model that charges nothing it holds trivially,
    see [zero_cost_trivial]); the machine-model statements are
    [ExactPolyDecider] and [PolySearch] below. *)
Definition CostModel : Type := (CNF -> bool) -> CNF -> nat.

(** Schema (abstract cost model, not the machine model): an exact SAT
    decider whose cost in [Cost] is polynomially bounded in [size]. *)
Definition ExactPolyDeciderFor (Cost : CostModel) : Prop :=
  exists dec c k, Decides dec /\ forall psi, Cost dec psi <= polyEval c k (size psi).

(** Schema (abstract cost model): a decider whose self-reduction finds a
    satisfying assignment of every satisfiable CNF at polynomial total query
    cost. *)
Definition PolySearchFor (Cost : CostModel) : Prop :=
  exists dec c k, forall phi,
    (Satisfiable phi -> evalCNF (fst (fullSearch dec phi)) phi = true) /\
    searchCost dec (Cost dec) (varsOf phi) phi <= polyEval c (k + 1) (size phi).

(** Decision to search, schema form: for every cost model, a polynomially
    bounded exact decider yields polynomial search with total query cost
    [c (size phi + 1)^(k+1)]. *)
Theorem decision_to_search_for : forall Cost, ExactPolyDeciderFor Cost -> PolySearchFor Cost.
Proof.
  intros Cost [dec [c [k [Hdec Hc]]]]. exists dec, c, k. intros phi. split.
  - apply fullSearch_correct. exact Hdec.
  - eapply Nat.le_trans; [apply (searchCost_le dec (Cost dec) c k Hc)|].
    eapply Nat.le_trans; [|apply mul_polyEval_le].
    apply Nat.mul_le_mono_r. apply varsOf_length_le.
Qed.

(* ---------- An unconditional (exponential) decider ---------- *)

Definition satDec (phi : CNF) : bool := solve (varsOf phi) phi.

Theorem satDec_correct : Decides satDec.
Proof.
  intros phi. unfold satDec. apply solve_correct. apply varsOf_spec.
Qed.

(** The schema is trivial in the cost model that charges nothing. *)
Theorem zero_cost_trivial : ExactPolyDeciderFor (fun _ _ => 0).
Proof.
  exists satDec, 0, 0. split; [exact satDec_correct | intros; lia].
Qed.

Theorem unconditional_search : forall phi, Satisfiable phi ->
  evalCNF (fst (fullSearch satDec phi)) phi = true.
Proof.
  intros phi Hs. apply fullSearch_correct; [exact satDec_correct | exact Hs].
Qed.

(* ---------- The shared machine model ---------- *)

(** The Machines.v names [Lit], [Clause], [CNF], [evalLit], [evalClause],
    [evalCNF], [Satisfiable], [mkLit] are shadowed by this file's own
    definitions and are written with the qualifier [Machines.] below. *)

(** The shared layer's literal with the same variable and polarity. *)
Definition toMLit (l : Lit) : Machines.Lit := Machines.mkLit (var l) (pos l).

(** A CNF of this file as a CNF of the shared layer. *)
Definition toM (phi : CNF) : Machines.CNF := map (map toMLit) phi.

(** The word encoding of a CNF (the shared layer's [encodeCNF]). *)
Definition enc (phi : CNF) : Word := encodeCNF (toM phi).

(** Encoding length, the input size of the machine model. *)
Definition encLen (phi : CNF) : nat := length (enc phi).

Theorem evalCNF_toM : forall (a : Assignment) (phi : CNF),
  Machines.evalCNF a (toM phi) = evalCNF a phi.
Proof.
  intros a phi. induction phi as [|C phi IH]; [reflexivity|].
  assert (hC : Machines.evalClause a (map toMLit C) = evalClause a C).
  { induction C as [|l C IHC]; [reflexivity|].
    cbn [map Machines.evalClause evalClause]. rewrite IHC.
    unfold Machines.evalLit, evalLit, toMLit. simpl.
    destruct (pos l), (a (var l)); reflexivity. }
  cbn [toM map Machines.evalCNF evalCNF]. unfold toM in IH. rewrite hC, IH. reflexivity.
Qed.

Theorem satisfiable_toM : forall phi, Machines.Satisfiable (toM phi) <-> Satisfiable phi.
Proof.
  intro phi. split.
  - intros [a h]. exists a. rewrite <- evalCNF_toM. exact h.
  - intros [a h]. exists a. rewrite evalCNF_toM. exact h.
Qed.

Theorem sat_enc : forall phi, SAT (enc phi) = true <-> Satisfiable phi.
Proof. intro phi. unfold enc. rewrite sat_encode. apply satisfiable_toM. Qed.

Theorem length_encodeClause_removeVar : forall v C,
  length (encodeClause (map toMLit (removeVar v C))) <=
    length (encodeClause (map toMLit C)).
Proof.
  intros v C. induction C as [|l C IH]; [cbn; lia|].
  cbn [removeVar]. destruct (Nat.eqb (var l) v).
  - cbn [map encodeClause]. rewrite length_app. lia.
  - cbn [map encodeClause]. rewrite !length_app. lia.
Qed.

(** Restriction never lengthens the encoding. *)
Theorem encLen_restrict_le : forall v b phi, encLen (restrict v b phi) <= encLen phi.
Proof.
  intros v b phi. unfold encLen, enc, toM. induction phi as [|C phi IH]; [cbn; lia|].
  pose proof (length_encodeClause_removeVar v C) as hC.
  cbn [restrict]. destruct (clauseHas v b C).
  - cbn [map encodeCNF]. rewrite length_app. lia.
  - cbn [map encodeCNF]. rewrite !length_app. lia.
Qed.

Theorem length_encodeClause_ge : forall C, length C + 1 <= length (encodeClause (map toMLit C)).
Proof.
  intro C. induction C as [|l C IH]; [cbn; lia|].
  cbn [map encodeClause]. unfold encodeLit. rewrite !length_app. cbn [length] in *. lia.
Qed.

(** The literal-count size is at most the encoding length. *)
Theorem size_le_encLen : forall phi, size phi <= encLen phi.
Proof.
  intro phi. unfold encLen, enc, toM. induction phi as [|C phi IH]; [cbn; lia|].
  pose proof (length_encodeClause_ge C).
  cbn [size map encodeCNF]. rewrite length_app. lia.
Qed.

(** Step-bounded step counter: the [Run] step count of [m] from [c] if it
    halts within [fuel] steps. *)
Fixpoint timeFor (m : Machine) (c : Config) (fuel : nat) : option nat :=
  match fuel with
  | 0 => None
  | S f => match step m c with
           | inl _ => Some 1
           | inr c' => option_map S (timeFor m c' f)
           end
  end.

Theorem timeFor_of_run : forall m c t b, Run m c t b ->
  forall fuel, t <= fuel -> timeFor m c fuel = Some t.
Proof.
  intros m c t b h. induction h as [c b hs | c c' t b hs _ IH]; intros fuel hf;
    (destruct fuel as [| fuel]; [lia |]); simpl; rewrite hs; [reflexivity |].
  rewrite IH by lia. reflexivity.
Qed.

(** The answer of machine [m] on input [x] when it halts within [p(|x|)]
    steps ([false] otherwise).  Lean's [machineDec m x] is the classical
    unclocked answer; Rocq clocks it by an explicit polynomial [p]. *)
Definition machineDec (m : Machine) (p : Polynomial) (x : Word) : bool :=
  match runFor m (initial x) (evalPoly p (length x)) with
  | Some b => b
  | None => false
  end.

(** The [Run] step count of [m] on [x] when it halts within [p(|x|)] steps
    ([0] otherwise). *)
Definition runTime (m : Machine) (p : Polynomial) (x : Word) : nat :=
  match timeFor m (initial x) (evalPoly p (length x)) with
  | Some t => t
  | None => 0
  end.

Theorem machineDec_eq : forall m p x t b, Run m (initial x) t b ->
  t <= evalPoly p (length x) -> machineDec m p x = b.
Proof.
  intros m p x t b h ht. unfold machineDec. rewrite (runFor_of_run _ _ _ _ h _ ht).
  reflexivity.
Qed.

Theorem runTime_eq : forall m p x t b, Run m (initial x) t b ->
  t <= evalPoly p (length x) -> runTime m p x = t.
Proof.
  intros m p x t b h ht. unfold runTime. rewrite (timeFor_of_run _ _ _ _ h _ ht).
  reflexivity.
Qed.

(** A machine deciding [SAT] decides satisfiability of every CNF of this
    file. *)
Theorem decides_of_decidesWithin : forall m p, DecidesWithin m p SAT ->
  Decides (fun psi => machineDec m p (enc psi)).
Proof.
  intros m p h psi. destruct (h (enc psi)) as [t [b [ht [hr hb]]]].
  cbn beta. rewrite (machineDec_eq _ _ _ _ _ hr ht), hb. apply sat_enc.
Qed.

(** Open obligation.  An exact SAT decider in the machine model: one
    [Machine] decides [SAT] within a polynomial number of [Run] steps.  This
    is [InP SAT] ([polyDec_iff_inP]); the self-reduction below shows it also
    gives polynomial-time search. *)
Definition ExactPolyDecider : Prop := PolyDec SAT.

(** Polynomial search in the machine model: a machine that halts within
    [p(|x|)] steps on every input, whose answers drive the self-reduction to
    a satisfying assignment of every satisfiable CNF, with total [Run] step
    count of all questions bounded by a polynomial in the encoding length. *)
Definition PolySearch : Prop :=
  exists (m : Machine) (p q : Polynomial),
    (forall x, exists t b, t <= evalPoly p (length x) /\ Run m (initial x) t b) /\
    forall phi,
      (Satisfiable phi ->
         evalCNF (fst (fullSearch (fun psi => machineDec m p (enc psi)) phi)) phi = true) /\
      searchCost (fun psi => machineDec m p (enc psi)) (fun psi => runTime m p (enc psi))
        (varsOf phi) phi <= evalPoly q (encLen phi).

(** [n * c (n+1)^d <= c (n+1)^(d+1)]. *)
Theorem mul_eval_le : forall (p : Polynomial) n,
  n * evalPoly p n <=
    evalPoly {| coefficient := coefficient p; degree := degree p + 1 |} n.
Proof. intros p n. exact (mul_polyEval_le (coefficient p) (degree p) n). Qed.

(** Decision to search in the machine model: from a polynomial-time machine
    decider for [SAT], the self-reduction finds a satisfying assignment of
    every satisfiable CNF, asking at most [size phi] questions whose total
    [Run] step count is at most [size phi * p(encLen phi)], a polynomial in
    the encoding length. *)
Theorem decision_to_search : ExactPolyDecider -> PolySearch.
Proof.
  intros [m [p hm]].
  pose proof (decides_of_decidesWithin m p hm) as hdec.
  assert (hcost : forall psi, runTime m p (enc psi) <= evalPoly p (encLen psi)).
  { intro psi. destruct (hm (enc psi)) as [t [b [ht [hr _]]]].
    rewrite (runTime_eq _ _ _ _ _ hr ht). exact ht. }
  exists m, p, {| coefficient := coefficient p; degree := degree p + 1 |}.
  split.
  - intro x. destruct (hm x) as [t [b [ht [hr _]]]]. exists t, b. auto.
  - intro phi. split.
    + apply fullSearch_correct. exact hdec.
    + pose proof (searchCost_le_measure (fun psi => machineDec m p (enc psi))
        (fun psi => runTime m p (enc psi)) encLen (evalPoly p)
        (fun a b hab => polynomial_eval_mono p a b hab) encLen_restrict_le hcost
        (varsOf phi) phi) as h1.
      assert (h2 : length (varsOf phi) <= encLen phi)
        by exact (Nat.le_trans _ _ _ (varsOf_length_le phi) (size_le_encLen phi)).
      eapply Nat.le_trans; [exact h1 |].
      eapply Nat.le_trans; [apply Nat.mul_le_mono_r; exact h2 |].
      apply mul_eval_le.
Qed.

(** Conditional theorem: the obligation is [InP SAT]. *)
Theorem inP_sat_of_exactPolyDecider : ExactPolyDecider -> InP SAT.
Proof. intro h. exact (proj1 (polyDec_iff_inP SAT) h). Qed.

(** Conditional theorem: with the NP-hardness half of Cook-Levin
    ([SATHard], a known theorem used only as an explicit premise), the
    obligation gives P = NP. *)
Theorem pEqualsNP_of_exactPolyDecider : SATHard -> ExactPolyDecider -> PEqualsNP.
Proof.
  intros hard h. exact (pEqualsNP_of_inP_sat hard (inP_sat_of_exactPolyDecider h)).
Qed.

(** Non-vacuity: polynomial-time machine decidability, the property that
    [ExactPolyDecider] asserts of [SAT], fails for some language. *)
Theorem exists_not_polyDec : exists L : Language, ~ PolyDec L.
Proof.
  destruct exists_not_inP as [L hL]. exists L. intro h.
  exact (hL (proj1 (polyDec_iff_inP L) h)).
Qed.
