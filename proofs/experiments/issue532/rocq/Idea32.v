(* Issue #532, Idea 32: promise algorithms.

   Verdict: developed to an open obligation (conditional theorem proved).

   A promise algorithm for L on a promise P only has to be correct on inputs
   satisfying P.  Negative (flip_at): for every promise and language over a type
   with decidable equality, an input x outside P allows an algorithm correct on
   all of P and wrong at x; hence promise correctness is total correctness
   exactly when P covers every input (promise_total_iff).  Conditional positive
   (promise_reduction_total): a map f into P with L x = M (f x) composes with any
   promise solver for M into a total solver for L, with additive cost
   (compose_cost); the "into P" condition is necessary (composition_works_iff).
   For CNF: the Unique-SAT promise excludes x0 \/ x1 (not_unique_example), so
   some promise-correct algorithm is wrong on it (usat_solver_wrong); another
   promise makes SAT trivial (trivial_promise_solver).  The open obligation is a
   deterministic polynomial-time isolation map (IsolationObligation), which with
   a promise solver decides SAT (isolation_solves_sat).  Nothing here decides
   P vs NP. *)

From Stdlib Require Import Bool Arith PeanoNat List Lia.
Import ListNotations.

(* General promise problems *)

Definition CorrectOn {A : Type} (P : A -> Prop) (L Alg : A -> bool) : Prop :=
  forall x, P x -> Alg x = L x.

(* Flip at x: an input outside the promise allows an algorithm correct on the
   whole promise and wrong at x. *)
Theorem flip_at {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y})
  (P : A -> Prop) (L : A -> bool) (x : A) :
  ~ P x -> exists Alg : A -> bool, CorrectOn P L Alg /\ Alg x <> L x.
Proof.
  intro hx.
  exists (fun y => if eq_dec y x then negb (L x) else L y). split.
  - intros y hy. destruct (eq_dec y x) as [e|ne].
    + subst y. contradiction.
    + reflexivity.
  - destruct (eq_dec x x) as [_|ne]; [|contradiction].
    destruct (L x); discriminate.
Qed.

(* Promise-correct algorithms need not be total. *)
Theorem promise_correct_not_total {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y})
  (P : A -> Prop) (L : A -> bool) :
  (exists x, ~ P x) ->
  exists Alg : A -> bool, CorrectOn P L Alg /\ ~ (forall y, Alg y = L y).
Proof.
  intros (x & hx).
  destruct (flip_at eq_dec P L x hx) as (Alg & hA & hne).
  exists Alg. split; [exact hA|]. intro hall. apply hne. apply hall.
Qed.

(* Conditional positive: a map into the promise preserving the answer turns any
   promise solver for M into a total solver for L. *)
Theorem promise_reduction_total {A B : Type} (P : B -> Prop) (L : A -> bool) (M : B -> bool)
  (f : A -> B) :
  (forall x, P (f x)) -> (forall x, L x = M (f x)) ->
  forall Alg : B -> bool, CorrectOn P M Alg -> forall x, Alg (f x) = L x.
Proof.
  intros hinto hpres Alg hA x. rewrite (hA (f x) (hinto x)), hpres. reflexivity.
Qed.

(* The "into the promise" condition is exactly what makes the composition work
   for every promise solver. *)
Theorem composition_works_iff {A B : Type} (eq_dec : forall x y : B, {x = y} + {x <> y})
  (P : B -> Prop) (Pdec : forall y, {P y} + {~ P y})
  (L : A -> bool) (M : B -> bool) (f : A -> B) :
  (forall x, L x = M (f x)) ->
  ((forall Alg : B -> bool, CorrectOn P M Alg -> forall x, Alg (f x) = L x) <->
   forall x, P (f x)).
Proof.
  intro hpres. split.
  - intros h x. destruct (Pdec (f x)) as [hx|hx]; [exact hx|].
    destruct (flip_at eq_dec P M (f x) hx) as (Alg & hA & hne).
    exfalso. apply hne. rewrite (h Alg hA x). apply hpres.
  - intros hinto Alg hA. exact (promise_reduction_total P L M f hinto hpres Alg hA).
Qed.

(* Special case f = id. *)
Theorem promise_total_iff {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y})
  (P : A -> Prop) (Pdec : forall y, {P y} + {~ P y}) (L : A -> bool) :
  (forall Alg : A -> bool, CorrectOn P L Alg -> forall x, Alg x = L x) <-> forall x, P x.
Proof.
  exact (composition_works_iff eq_dec P Pdec L L (fun x => x) (fun _ => eq_refl)).
Qed.

(* Cost of the composition with abstract step counts and sizes. *)
Theorem compose_cost {A B : Type} (sizeA : A -> nat) (sizeB : B -> nat) (f : A -> B)
  (costF : A -> nat) (costA : B -> nat) (p q r : nat -> nat) :
  (forall x, costF x <= p (sizeA x)) -> (forall x, sizeB (f x) <= q (sizeA x)) ->
  (forall y, costA y <= r (sizeB y)) -> (forall m m', m <= m' -> r m <= r m') ->
  forall x, costF x + costA (f x) <= p (sizeA x) + r (q (sizeA x)).
Proof.
  intros hF hS hA hr x. apply Nat.add_le_mono; [apply hF|].
  eapply Nat.le_trans; [apply hA|]. apply hr. apply hS.
Qed.

(* CNF core *)

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

Definition lit_eq_dec (l1 l2 : Lit) : {l1 = l2} + {l1 <> l2}.
Proof. decide equality; [apply bool_dec|apply Nat.eq_dec]. Defined.

Definition cnf_eq_dec : forall phi psi : CNF, {phi = psi} + {phi <> psi} :=
  list_eq_dec (list_eq_dec lit_eq_dec).

(* The Unique-SAT promise *)

Definition AtMostOneSolution (phi : CNF) : Prop :=
  forall a b, evalCNF a phi = true -> evalCNF b phi = true ->
    forall v, In v (vars phi) -> a v = b v.

(* The formula x0 \/ x1. *)
Definition twoWay : CNF := [[mkLit 0 true; mkLit 1 true]].

Theorem twoWay_satisfiable : Satisfiable twoWay.
Proof. exists (fun _ => true). reflexivity. Qed.

(* x0 \/ x1 has two solutions differing on x1, so it violates the promise. *)
Theorem not_unique_example : ~ AtMostOneSolution twoWay.
Proof.
  intro h.
  pose proof (h (fun _ => true) (fun v => Nat.eqb v 0) eq_refl eq_refl 1
    (or_intror (or_introl eq_refl))) as e.
  discriminate e.
Qed.

(* The single-literal formula x0 satisfies the promise. *)
Theorem unique_example : AtMostOneSolution [[mkLit 0 true]].
Proof.
  intros a b ha hb v hv. simpl in ha, hb, hv. unfold evalLit in ha, hb. simpl in ha, hb.
  destruct hv as [e|[]]. subst v.
  destruct (a 0), (b 0); simpl in ha, hb; congruence.
Qed.

(* flip_at instantiated to Unique-SAT. *)
Theorem usat_solver_wrong (sat : CNF -> bool)
  (hsat : forall phi, sat phi = true <-> Satisfiable phi) :
  exists Alg : CNF -> bool, CorrectOn AtMostOneSolution sat Alg /\
    Alg twoWay = false /\ Satisfiable twoWay.
Proof.
  destruct (flip_at cnf_eq_dec AtMostOneSolution sat twoWay not_unique_example)
    as (Alg & hA & hne).
  assert (hs : sat twoWay = true) by (apply hsat; exact twoWay_satisfiable).
  exists Alg. split; [exact hA|]. split; [|exact twoWay_satisfiable].
  destruct (Alg twoWay) eqn:h; [|reflexivity].
  exfalso. apply hne. rewrite hs. reflexivity.
Qed.

(* A promise that makes SAT trivial *)

Fixpoint hasEmpty (phi : CNF) : bool :=
  match phi with
  | [] => false
  | c :: phi' => match c with [] => true | _ => false end || hasEmpty phi'
  end.

Theorem hasEmpty_unsat (phi : CNF) : hasEmpty phi = true -> ~ Satisfiable phi.
Proof.
  intros h (a & ha). induction phi as [|c phi IH]; [discriminate|].
  simpl in h, ha. apply andb_true_iff in ha. destruct ha as [hc hphi].
  destruct c as [|l c].
  - discriminate.
  - simpl in h. apply IH; assumption.
Qed.

Definition EmptyPromise (phi : CNF) : Prop := Satisfiable phi \/ hasEmpty phi = true.

(* On this promise the linear-time test "no empty clause" decides SAT. *)
Theorem trivial_promise_solver (sat : CNF -> bool)
  (hsat : forall phi, sat phi = true <-> Satisfiable phi) :
  CorrectOn EmptyPromise sat (fun phi => negb (hasEmpty phi)).
Proof.
  intros phi hphi. destruct (hasEmpty phi) eqn:he.
  - pose proof (hasEmpty_unsat phi he) as hn. simpl.
    destruct (sat phi) eqn:hs; [|reflexivity].
    exfalso. apply hn. apply hsat. exact hs.
  - assert (hS : Satisfiable phi) by (destruct hphi as [h|h]; [exact h|congruence]).
    simpl. symmetry. apply hsat. exact hS.
Qed.

(* The same trivial solver is wrong outside the promise, on x0 /\ ~x0. *)
Theorem trivial_solver_wrong (sat : CNF -> bool)
  (hsat : forall phi, sat phi = true <-> Satisfiable phi) :
  (fun phi => negb (hasEmpty phi)) [[mkLit 0 true]; [mkLit 0 false]] <>
    sat [[mkLit 0 true]; [mkLit 0 false]].
Proof.
  simpl. intro h. symmetry in h. apply hsat in h. destruct h as (a & ha).
  simpl in ha. unfold evalLit in ha. simpl in ha. destruct (a 0); discriminate.
Qed.

(* The open obligation *)

Definition IsolationObligation (PolyTime : (CNF -> CNF) -> Prop) : Prop :=
  exists f : CNF -> CNF, PolyTime f /\ (forall phi, AtMostOneSolution (f phi)) /\
    forall phi, Satisfiable phi <-> Satisfiable (f phi).

(* Conditional theorem: the obligation plus a promise solver gives a total SAT solver. *)
Theorem isolation_solves_sat (PolyTime : (CNF -> CNF) -> Prop) :
  IsolationObligation PolyTime ->
  forall Alg : CNF -> bool,
    (forall phi, AtMostOneSolution phi -> (Alg phi = true <-> Satisfiable phi)) ->
    exists f : CNF -> CNF, PolyTime f /\ forall phi, Alg (f phi) = true <-> Satisfiable phi.
Proof.
  intros (f & hf & hinto & hpres) Alg hA. exists f. split; [exact hf|].
  intro phi. rewrite (hA (f phi) (hinto phi)). symmetry. apply hpres.
Qed.

Definition isolate (sat : CNF -> bool) (phi : CNF) : CNF := if sat phi then [] else [[]].

(* A SAT decider meets the correctness part of the obligation trivially. *)
Theorem decider_meets_isolation (sat : CNF -> bool)
  (hsat : forall phi, sat phi = true <-> Satisfiable phi) :
  (forall phi, AtMostOneSolution (isolate sat phi)) /\
  forall phi, Satisfiable phi <-> Satisfiable (isolate sat phi).
Proof.
  split.
  - intros phi a b ha _ v hv. unfold isolate in ha, hv.
    destruct (sat phi); simpl in ha, hv; [contradiction|discriminate].
  - intro phi. unfold isolate. destruct (sat phi) eqn:hs.
    + split; intro h; [exists (fun _ => true); reflexivity|apply hsat; exact hs].
    + split.
      * intro h. apply hsat in h. congruence.
      * intros (a & ha). discriminate.
Qed.
