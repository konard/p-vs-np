(* Issue #532, Idea 31: length-wise advice (truth-table circuits).

   Verdict: refuted as a route (general theorem).

   Non-uniformly the idea is correct and general: every Boolean function on
   n-bit inputs is computed by the complete decision tree build n f
   (build_correct), with exactly 2 ^ n leaves and 2 ^ (n + 1) - 1 nodes
   (build_leaves, build_size); its leaves are the truth table
   (build_leafList); the advice is exactly 2 ^ n bits and determines the
   function (advice_length, advice_injective, ofTable_advice); no fixed
   advice length below 2 ^ n works for all functions (no_shorter_advice).
   As a route to uniform algorithms it fails: parity needs 2 ^ n leaves
   (parity_tree_leaves), and every enumeration of uniform deciders misses a
   length-only language with one-node trees at every length
   (advice_beyond_uniform).

   Machine model (Machines.v, Circuits.v): UniformAdvice L asks for advice
   adv n attached to the input by a polynomial-time Machine (so the advice is
   uniform and of polynomial length) and a polynomial-time machine deciding L
   from the input with its advice.  The open obligation is
   UniformSATAdvice := UniformAdvice SAT; inP_sat_of_uniformSATAdvice and
   pEqualsNP_of_uniformSATAdvice derive InP SAT and PEqualsNP from it,
   not_uniformSATAdvice_of_superpoly shows that a superpolynomial circuit
   lower bound for SAT refutes it (given the named known theorem
   PSubsetPPoly), not_forall_uniformAdvice is the non-vacuity check, and
   uniformPolyAdviceFor_of_uniformAdvice instantiates the schema
   UniformPolyAdviceFor.

   Difference from Lean: not_uniformSATAdvice_of_superpoly uses the
   constructive direction Circuits.not_inPPoly_of_superpoly instead of
   superpoly_iff_not_inPPoly (which in Rocq takes excluded middle as a
   premise).  No axioms are used.

   Nothing here decides P vs NP. *)

From Stdlib Require Import Bool Arith PeanoNat List Lia.
Import ListNotations.
From proofs.experiments.issue532.rocq Require Import Machines Circuits.

(* Binary decision trees: node lo hi reads the next input bit. *)
Inductive DTree : Type :=
| leaf : bool -> DTree
| node : DTree -> DTree -> DTree.

Fixpoint teval (T : DTree) (x : list bool) : bool :=
  match T, x with
  | leaf b, _ => b
  | node _ _, [] => false
  | node lo hi, b :: x' => if b then teval hi x' else teval lo x'
  end.

Fixpoint leaves (T : DTree) : nat :=
  match T with
  | leaf _ => 1
  | node lo hi => leaves lo + leaves hi
  end.

(* Total number of nodes (leaves included). *)
Fixpoint size (T : DTree) : nat :=
  match T with
  | leaf _ => 1
  | node lo hi => size lo + size hi + 1
  end.

Fixpoint leafList (T : DTree) : list bool :=
  match T with
  | leaf b => [b]
  | node lo hi => leafList lo ++ leafList hi
  end.

(* The complete decision tree (table lookup) of f on inputs of length n. *)
Fixpoint build (n : nat) (f : list bool -> bool) : DTree :=
  match n with
  | 0 => leaf (f [])
  | S n' => node (build n' (fun x => f (false :: x))) (build n' (fun x => f (true :: x)))
  end.

(* The table-lookup tree is correct on every input of length n, for every n. *)
Theorem build_correct (n : nat) (f : list bool -> bool) (x : list bool) :
  length x = n -> teval (build n f) x = f x.
Proof.
  revert f x. induction n as [|n IH]; intros f x h.
  - destruct x; [reflexivity|discriminate].
  - destruct x as [|b x]; [discriminate|]. simpl in h. injection h as h.
    destruct b; simpl; [apply (IH (fun y => f (true :: y)) x h)|apply (IH (fun y => f (false :: y)) x h)].
Qed.

(* Exactly 2 ^ n leaves. *)
Theorem build_leaves (n : nat) (f : list bool -> bool) : leaves (build n f) = 2 ^ n.
Proof.
  revert f. induction n as [|n IH]; intro f; simpl; [reflexivity|].
  rewrite !IH. lia.
Qed.

(* Exactly 2 ^ (n + 1) - 1 nodes. *)
Theorem build_size (n : nat) (f : list bool -> bool) : size (build n f) + 1 = 2 ^ (n + 1).
Proof.
  revert f. induction n as [|n IH]; intro f; simpl; [reflexivity|].
  pose proof (IH (fun x => f (false :: x))) as h1.
  pose proof (IH (fun x => f (true :: x))) as h2.
  lia.
Qed.

(* All inputs of length n, false-prefixed ones first. *)
Fixpoint allBool (n : nat) : list (list bool) :=
  match n with
  | 0 => [[]]
  | S n' => map (cons false) (allBool n') ++ map (cons true) (allBool n')
  end.

Theorem allBool_length (n : nat) : length (allBool n) = 2 ^ n.
Proof.
  induction n as [|n IH]; simpl; [reflexivity|].
  rewrite length_app, !length_map, IH. lia.
Qed.

Theorem mem_allBool (n : nat) (x : list bool) : In x (allBool n) <-> length x = n.
Proof.
  revert x. induction n as [|n IH]; intro x; simpl.
  - split; [intros [e|[]]; subst; reflexivity|].
    intro h. destruct x; [left; reflexivity|discriminate].
  - rewrite in_app_iff, !in_map_iff. split.
    + intros [(w & e & hw)|(w & e & hw)]; subst x; simpl; apply IH in hw; lia.
    + intro h. destruct x as [|b w]; [discriminate|]. simpl in h.
      assert (hw : In w (allBool n)) by (apply IH; lia).
      destruct b; [right|left]; exists w; split; auto.
Qed.

Lemma nodup_map_cons (a : bool) (W : list (list bool)) :
  NoDup W -> NoDup (map (cons a) W).
Proof.
  induction W as [|v W IH]; intro h; simpl; [constructor|].
  inversion h as [|v' W' hv hW]; subst. constructor; [|apply IH; exact hW].
  intro Hin. apply in_map_iff in Hin. destruct Hin as (u & e & hu).
  injection e as e. subst u. contradiction.
Qed.

Lemma nodup_app_intro {A : Type} (l1 l2 : list A) :
  NoDup l1 -> NoDup l2 -> (forall x, In x l1 -> ~ In x l2) -> NoDup (l1 ++ l2).
Proof.
  induction l1 as [|a l1 IH]; intros h1 h2 hd; simpl; [exact h2|].
  inversion h1 as [|a' l1' ha hl1]; subst. constructor.
  - rewrite in_app_iff. intros [h|h]; [contradiction|].
    apply (hd a); [left; reflexivity|exact h].
  - apply IH; [exact hl1|exact h2|]. intros x hx. apply hd. right. exact hx.
Qed.

Theorem allBool_nodup (n : nat) : NoDup (allBool n).
Proof.
  induction n as [|n IH]; simpl.
  - constructor; [intros []|constructor].
  - apply nodup_app_intro; [apply nodup_map_cons; exact IH|apply nodup_map_cons; exact IH|].
    intros x hx hy. apply in_map_iff in hx, hy.
    destruct hx as (u & eu & _). destruct hy as (v & ev & _). subst x. discriminate.
Qed.

(* The leaves of the table-lookup tree are the truth table of f. *)
Theorem build_leafList (n : nat) (f : list bool -> bool) :
  leafList (build n f) = map f (allBool n).
Proof.
  revert f. induction n as [|n IH]; intro f; simpl; [reflexivity|].
  rewrite !IH, map_app, !map_map. reflexivity.
Qed.

(* The advice string for length n: the truth table. *)
Definition advice (n : nat) (f : list bool -> bool) : list bool := leafList (build n f).

(* The advice is exactly 2 ^ n bits. *)
Theorem advice_length (n : nat) (f : list bool -> bool) : length (advice n f) = 2 ^ n.
Proof. unfold advice. rewrite build_leafList, length_map, allBool_length. reflexivity. Qed.

(* Rebuild a tree from a table. *)
Fixpoint ofTable (n : nat) (t : list bool) : DTree :=
  match n with
  | 0 => leaf (hd false t)
  | S n' => node (ofTable n' (firstn (2 ^ n') t)) (ofTable n' (skipn (2 ^ n') t))
  end.

Lemma firstn_app_exact {A : Type} (l1 l2 : list A) : firstn (length l1) (l1 ++ l2) = l1.
Proof. induction l1 as [|a l1 IH]; simpl; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma skipn_app_exact {A : Type} (l1 l2 : list A) : skipn (length l1) (l1 ++ l2) = l2.
Proof. induction l1 as [|a l1 IH]; simpl; [reflexivity|]. exact IH. Qed.

(* Decoding the advice recovers the table-lookup tree. *)
Theorem ofTable_advice (n : nat) (f : list bool -> bool) :
  ofTable n (advice n f) = build n f.
Proof.
  revert f. induction n as [|n IH]; intro f; [reflexivity|].
  pose proof (advice_length n (fun x => f (false :: x))) as h1.
  unfold advice in h1 |- *. simpl.
  rewrite <- h1, firstn_app_exact, skipn_app_exact.
  pose proof (IH (fun x => f (false :: x))) as e1.
  pose proof (IH (fun x => f (true :: x))) as e2.
  unfold advice in e1, e2. rewrite e1, e2. reflexivity.
Qed.

(* The advice determines the function on inputs of length n. *)
Theorem advice_injective (n : nat) (f g : list bool -> bool) :
  advice n f = advice n g -> forall x, length x = n -> f x = g x.
Proof.
  intros h x hx.
  rewrite <- (build_correct n f x hx), <- (build_correct n g x hx).
  rewrite <- (ofTable_advice n f), <- (ofTable_advice n g), h. reflexivity.
Qed.

(* Every table of length 2 ^ n is realised: the table of ofTable n t is t. *)
Theorem table_of_ofTable (n : nat) (t : list bool) :
  length t = 2 ^ n -> map (teval (ofTable n t)) (allBool n) = t.
Proof.
  revert t. induction n as [|n IH]; intros t h.
  - destruct t as [|b [|c t]]; simpl in h; try lia. reflexivity.
  - simpl allBool. rewrite map_app, !map_map.
    change (fun x => teval (ofTable (S n) t) (false :: x))
      with (teval (ofTable n (firstn (2 ^ n) t))).
    change (fun x => teval (ofTable (S n) t) (true :: x))
      with (teval (ofTable n (skipn (2 ^ n) t))).
    assert (ht : length (firstn (2 ^ n) t) = 2 ^ n)
      by (rewrite length_firstn, h; simpl; lia).
    assert (hd : length (skipn (2 ^ n) t) = 2 ^ n)
      by (rewrite length_skipn, h; simpl; lia).
    rewrite (IH _ ht), (IH _ hd). apply firstn_skipn.
Qed.

(* Pigeonhole: a duplicate-free list covered by the image of codes is no longer. *)
Theorem cover_length {Code : Type} (decode : Code -> list bool)
  (targets : list (list bool)) (codes : list Code) :
  NoDup targets ->
  (forall t, In t targets -> exists c, In c codes /\ decode c = t) ->
  length targets <= length codes.
Proof.
  intros hnd hcov.
  rewrite <- (length_map decode codes).
  apply NoDup_incl_length; [exact hnd|].
  intros t ht. destruct (hcov t ht) as (c & hc & e).
  apply in_map_iff. exists c. split; assumption.
Qed.

Lemma uncovered_or_cover {Code : Type} (decode : Code -> list bool)
  (codes : list Code) (targets : list (list bool)) :
  (exists t, In t targets /\ forall c, In c codes -> decode c <> t) \/
  (forall t, In t targets -> exists c, In c codes /\ decode c = t).
Proof.
  induction targets as [|t targets IH].
  - right. intros t [].
  - destruct (in_dec (list_eq_dec bool_dec) t (map decode codes)) as [hin|hout].
    + destruct IH as [(u & hu & hno)|hall].
      * left. exists u. split; [right; exact hu|exact hno].
      * right. intros u [e|hu].
        -- subst u. apply in_map_iff in hin. destruct hin as (c & e & hc).
           exists c. split; assumption.
        -- apply hall. exact hu.
    + left. exists t. split; [left; reflexivity|].
      intros c hc e. apply hout. apply in_map_iff. exists c. split; assumption.
Qed.

Lemma differ_or_agree (f1 f2 : list bool -> bool) (l : list (list bool)) :
  (exists x, In x l /\ f1 x <> f2 x) \/ (forall x, In x l -> f1 x = f2 x).
Proof.
  induction l as [|x l IH].
  - right. intros x [].
  - destruct (bool_dec (f1 x) (f2 x)) as [e|ne].
    + destruct IH as [(y & hy & hne)|hall].
      * left. exists y. split; [right; exact hy|exact hne].
      * right. intros y [ey|hy]; [subst y; exact e|apply hall; exact hy].
    + left. exists x. split; [left; reflexivity|exact ne].
Qed.

(* No advice scheme with fixed length m < 2 ^ n handles all functions on length n. *)
Theorem no_shorter_advice (n m : nat) (decode : list bool -> list bool -> bool) :
  m < 2 ^ n ->
  exists f : list bool -> bool, forall a, length a = m ->
    exists x, length x = n /\ decode a x <> f x.
Proof.
  intro hm.
  assert (hlt : length (allBool m) < length (allBool (2 ^ n))).
  { rewrite !allBool_length. apply Nat.pow_lt_mono_r; lia. }
  destruct (uncovered_or_cover (fun a => map (decode a) (allBool n)) (allBool m)
    (allBool (2 ^ n))) as [(t & ht & hno)|hcov].
  - assert (htl : length t = 2 ^ n) by (apply mem_allBool in ht; exact ht).
    exists (teval (ofTable n t)). intros a ha.
    destruct (differ_or_agree (decode a) (teval (ofTable n t)) (allBool n))
      as [(x & hx & hne)|hall].
    + exists x. split; [apply mem_allBool; exact hx|exact hne].
    + exfalso. apply (hno a (proj2 (mem_allBool m a) ha)).
      rewrite <- (table_of_ofTable n t htl). apply map_ext_in. exact hall.
  - pose proof (cover_length (fun a => map (decode a) (allBool n)) _ _
      (allBool_nodup _) hcov). lia.
Qed.

(* Parity of a bit string. *)
Fixpoint parity (x : list bool) : bool :=
  match x with
  | [] => false
  | b :: x' => xorb b (parity x')
  end.

Lemma leaves_pos (T : DTree) : 1 <= leaves T.
Proof. induction T as [b|lo IHlo hi IHhi]; simpl; lia. Qed.

(* Any decision tree computing (possibly negated) parity on length n has at
   least 2 ^ n leaves. *)
Theorem parity_tree_leaves (n : nat) (T : DTree) (c : bool) :
  (forall x, length x = n -> teval T x = xorb c (parity x)) -> 2 ^ n <= leaves T.
Proof.
  revert T c. induction n as [|n IH]; intros T c h.
  - apply leaves_pos.
  - destruct T as [b|lo hi].
    + pose proof (h (false :: repeat false n)) as h0.
      pose proof (h (true :: repeat false n)) as h1.
      simpl in h0, h1. rewrite repeat_length in h0, h1.
      specialize (h0 eq_refl). specialize (h1 eq_refl).
      destruct c, (parity (repeat false n)); simpl in h0, h1; congruence.
    + assert (hlo : forall x, length x = n -> teval lo x = xorb c (parity x)).
      { intros x hx. pose proof (h (false :: x)) as hf. simpl in hf.
        rewrite hf by lia. destruct c, (parity x); reflexivity. }
      assert (hhi : forall x, length x = n -> teval hi x = xorb (negb c) (parity x)).
      { intros x hx. pose proof (h (true :: x)) as hf. simpl in hf.
        rewrite hf by lia. destruct c, (parity x); reflexivity. }
      pose proof (IH lo c hlo). pose proof (IH hi (negb c) hhi). simpl. lia.
Qed.

(* The complete tree for parity has exactly 2 ^ n leaves, so the bound is tight. *)
Theorem parity_tree_exact (n : nat) : leaves (build n parity) = 2 ^ n.
Proof. apply build_leaves. Qed.

(* Every length-only language has one-bit advice: a one-node tree at every length. *)
Theorem unary_one_bit (u : nat -> bool) (n : nat) :
  exists T : DTree, size T = 1 /\ forall x, length x = n -> teval T x = u (length x).
Proof.
  exists (leaf (u n)). split; [reflexivity|]. intros x hx. rewrite hx. reflexivity.
Qed.

(* For every enumeration of uniform deciders there is a length-only language with
   one-node trees at every length that no enumerated decider computes. *)
Theorem advice_beyond_uniform (e : nat -> list bool -> bool) :
  exists L : list bool -> bool,
    (forall n, exists T : DTree, size T = 1 /\ forall x, length x = n -> teval T x = L x) /\
    forall i, e i <> L.
Proof.
  set (u := fun n => negb (e n (repeat false n))).
  exists (fun x => u (length x)). split.
  - intro n. apply unary_one_bit.
  - intros i hi.
    pose proof (f_equal (fun g => g (repeat false i)) hi) as h. simpl in h.
    unfold u in h. rewrite repeat_length in h.
    destruct (e i (repeat false i)); discriminate.
Qed.

Record Poly := mkPoly { coefficient : nat; degree : nat }.

Definition eval (p : Poly) (n : nat) : nat := coefficient p * (n + 1) ^ degree p.

(** Schema for turning advice into a uniform algorithm: advice of polynomial
    length produced by a generator in a caller-supplied class Uniform, and an
    unrestricted decoder.  Uniform and decode are free, so the schema carries
    no running-time content; the machine version is UniformAdvice below. *)
Definition UniformPolyAdviceFor (Uniform : (nat -> list bool) -> Prop) (L : list bool -> bool) : Prop :=
  exists (gen : nat -> list bool) (decode : list bool -> list bool -> bool) (p : Poly),
    Uniform gen /\ (forall n, length (gen n) <= eval p n) /\
    forall x, decode (gen (length x)) x = L x.

(* Unpacking the schema: generator and decoder combine into one decider. *)
Theorem uniform_advice_decides (Uniform : (nat -> list bool) -> Prop) (L : list bool -> bool) :
  UniformPolyAdviceFor Uniform L ->
  exists (gen : nat -> list bool) (decode : list bool -> list bool -> bool),
    Uniform gen /\ forall x, decode (gen (length x)) x = L x.
Proof.
  intros (gen & decode & p & hu & _ & hc). exists gen, decode. split; assumption.
Qed.

(** ** The machine model: uniformly generated polynomial advice *)

(** Self-delimiting encoding of an advice string: each bit b becomes 1 b, and
    a final 0 ends the advice. *)
Fixpoint pack (a : Word) : Word :=
  match a with
  | [] => [false]
  | b :: a' => true :: b :: pack a'
  end.

(** Strip a packed advice prefix. *)
Fixpoint unpack (w : Word) : Word :=
  match w with
  | true :: _ :: w' => unpack w'
  | false :: w' => w'
  | _ => []
  end.

Theorem unpack_pack_append : forall a x : Word, unpack (pack a ++ x) = x.
Proof. intros a x. induction a as [| b a IH]; simpl; [reflexivity | exact IH]. Qed.

Theorem length_pack : forall a : Word, length (pack a) = 2 * length a + 1.
Proof. intro a. induction a as [| b a IH]; simpl; [reflexivity | rewrite IH; lia]. Qed.

(** The input [x] with the advice string [a] attached in front. *)
Definition adviceWord (a x : Word) : Word := pack a ++ x.

Theorem unpack_adviceWord : forall a x : Word, unpack (adviceWord a x) = x.
Proof. intros a x. apply unpack_pack_append. Qed.

(** Uniform polynomial advice in the machine model: a Machine m attaches the
    advice adv |x| to every input within p steps (so the advice is generated
    uniformly and has polynomial length), and a machine d decides L within q
    steps from the input with its advice attached. *)
Definition UniformAdvice (L : Language) : Prop :=
  exists (adv : nat -> Word) (m : Machine) (p : Polynomial) (d : Machine) (q : Polynomial),
    Computes m (fun x => adviceWord (adv (length x)) x) p /\
    DecidesOn d q (fun w => exists x, w = adviceWord (adv (length x)) x)
      (fun w => L (unpack w)).

(** Open obligation.  SAT has uniform polynomial advice: some length-indexed
    advice is attached to every input by a polynomial-time Machine, and a
    polynomial-time machine decides SAT from the input with its advice. *)
Definition UniformSATAdvice : Prop := UniformAdvice SAT.

(** Uniformly generated polynomial advice gives a polynomial-time decider. *)
Theorem inP_of_uniformAdvice : forall L : Language, UniformAdvice L -> InP L.
Proof.
  intros L [adv [m [p [d [q [hm hd]]]]]].
  apply (inP_of_promise_reduction L (fun w => L (unpack w))
    (fun w => exists x, w = adviceWord (adv (length x)) x) m d
    (fun x => adviceWord (adv (length x)) x) p q hm).
  - intro x. exists x. reflexivity.
  - intro x. rewrite unpack_adviceWord. reflexivity.
  - exact hd.
Qed.

(** Conditional theorem.  The open obligation puts SAT in P. *)
Theorem inP_sat_of_uniformSATAdvice : UniformSATAdvice -> InP SAT.
Proof. intro h. exact (inP_of_uniformAdvice SAT h). Qed.

(** Conditional theorem.  With the hardness half of Cook-Levin, the open
    obligation gives P = NP. *)
Theorem pEqualsNP_of_uniformSATAdvice : SATHard -> UniformSATAdvice -> PEqualsNP.
Proof.
  intros hard h. exact (pEqualsNP_of_inP_sat hard (inP_sat_of_uniformSATAdvice h)).
Qed.

(** Uniform advice is in particular non-uniform advice: with the known
    theorem PSubsetPPoly, the language has polynomial-size circuits. *)
Theorem inPPoly_of_uniformAdvice : PSubsetPPoly -> forall L : Language,
  UniformAdvice L -> InPPoly L.
Proof. intros hP L h. exact (hP L (inP_of_uniformAdvice L h)). Qed.

(** Refutation route.  A superpolynomial circuit lower bound for SAT
    (together with the known theorem PSubsetPPoly) refutes the open
    obligation. *)
Theorem not_uniformSATAdvice_of_superpoly : PSubsetPPoly ->
  SuperpolyLowerBound SAT -> ~ UniformSATAdvice.
Proof.
  intros hP h hU.
  exact (not_inPPoly_of_superpoly SAT h (inPPoly_of_uniformAdvice hP SAT hU)).
Qed.

(** Non-vacuity.  Some language has no uniform polynomial advice. *)
Theorem not_forall_uniformAdvice : ~ (forall L : Language, UniformAdvice L).
Proof.
  intro h. destruct exists_not_inP as [L hL].
  exact (hL (inP_of_uniformAdvice L (h L))).
Qed.

(** Schema instance.  Machine-generated advice instantiates
    UniformPolyAdviceFor, with Uniform the class of advice generators that a
    polynomial-time machine can attach to the input and decode the language
    decided by the query machine.  The length bound on the advice comes from
    the running time (computes_output_poly). *)
Theorem uniformPolyAdviceFor_of_uniformAdvice : forall L : Language, UniformAdvice L ->
  UniformPolyAdviceFor
    (fun gen => exists (m : Machine) (p : Polynomial),
      Computes m (fun x => adviceWord (gen (length x)) x) p)
    L.
Proof.
  intros L [adv [m [p [d [q [hm _]]]]]].
  destruct (computes_output_poly _ _ _ hm) as [r hr].
  exists adv, (fun a x => L (unpack (adviceWord a x))),
    (mkPoly (Complexity.coefficient r) (Complexity.degree r)).
  split; [exists m, p; exact hm |]. split.
  - intro n. pose proof (hr (repeat false n)) as hn.
    cbv beta in hn. unfold adviceWord in hn.
    rewrite length_app, length_pack, repeat_length in hn.
    unfold eval. simpl. unfold evalPoly in hn. lia.
  - intro x. rewrite unpack_adviceWord. reflexivity.
Qed.
