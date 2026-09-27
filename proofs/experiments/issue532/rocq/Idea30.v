(* Issue #532, Idea 30: unrestricted circuit lower bounds (transfer and counting).

   Verdict: developed to an open obligation (conditional theorem proved).

   lower_bound_transfer / no_fast_algorithm: a circuit lower bound, a
   simulation of fast algorithms by small circuits (a hypothesis here, i.e.
   P in P/poly is not proved in this file) and a size bound exclude a fast
   algorithm.  uncovered_table / shannon_circuits: Shannon counting.  Words of
   length s over an alphabet of size m number m ^ s; truth tables on n bits
   number 2 ^ (2 ^ n) and are duplicate-free; a shorter list of codes cannot
   cover them.  For NAND straight-line circuits, if
   (g + 1) * ((n + g) * (n + g)) ^ g < 2 ^ (2 ^ n) then some n-bit function
   has no circuit with at most g gates.  Counting is non-explicit; the open
   obligation ExplicitNPLowerBound asks for an explicit NP function with a
   superpolynomial lower bound.  Nothing here proves such a bound. *)

From Stdlib Require Import Bool Arith PeanoNat List Lia.
Import ListNotations.

(* The abstract conditional contradiction. *)
Theorem lower_bound_transfer (Algorithm Circuit : Type) (compile : Algorithm -> Circuit)
  (fast : Algorithm -> Prop) (correct expensive : Circuit -> Prop) :
  (forall c, correct c -> expensive c) ->
  (forall a, fast a -> correct (compile a)) ->
  (forall a, fast a -> ~ expensive (compile a)) ->
  forall a, ~ fast a.
Proof.
  intros Hlower Hsimulation Hsize a Hfast.
  apply (Hsize a Hfast). apply Hlower, Hsimulation, Hfast.
Qed.

(* Words over a finite alphabet. *)

Fixpoint consAll {A : Type} (l : list A) (W : list (list A)) : list (list A) :=
  match l with
  | [] => []
  | a :: l' => map (cons a) W ++ consAll l' W
  end.

Fixpoint words {A : Type} (alph : list A) (s : nat) : list (list A) :=
  match s with
  | 0 => [[]]
  | S s' => consAll alph (words alph s')
  end.

Lemma consAll_length {A : Type} (l : list A) (W : list (list A)) :
  length (consAll l W) = length l * length W.
Proof.
  induction l as [|a l IH]; simpl; [reflexivity|].
  rewrite length_app, length_map, IH. reflexivity.
Qed.

(* There are exactly m ^ s words of length s over an alphabet of size m. *)
Theorem words_length {A : Type} (alph : list A) (s : nat) :
  length (words alph s) = length alph ^ s.
Proof.
  induction s as [|s IH]; simpl; [reflexivity|].
  rewrite consAll_length, IH. reflexivity.
Qed.

Lemma mem_consAll {A : Type} (l : list A) (W : list (list A)) (w : list A) :
  In w (consAll l W) <-> exists a, In a l /\ exists v, In v W /\ w = a :: v.
Proof.
  induction l as [|b l IH]; simpl.
  - split; [intros []|intros (a & [] & _)].
  - rewrite in_app_iff, in_map_iff, IH. split.
    + intros [(v & e & hv) | (a & ha & v & hv & e)].
      * exists b. split; [left; reflexivity|]. exists v. split; [exact hv|symmetry; exact e].
      * exists a. split; [right; exact ha|]. exists v. split; [exact hv|exact e].
    + intros (a & [hab|ha] & v & hv & e).
      * subst a. left. exists v. split; [symmetry; exact e|exact hv].
      * right. exists a. split; [exact ha|]. exists v. split; [exact hv|exact e].
Qed.

(* words alph s contains exactly the words of length s over alph. *)
Theorem mem_words {A : Type} (alph : list A) (s : nat) (w : list A) :
  In w (words alph s) <-> length w = s /\ forall a, In a w -> In a alph.
Proof.
  revert w. induction s as [|s IH]; intro w; simpl.
  - split.
    + intros [e|[]]. subst w. split; [reflexivity|intros a []].
    + intros [hl _]. destruct w; [left; reflexivity|discriminate].
  - rewrite mem_consAll. split.
    + intros (a & ha & v & hv & e). subst w. apply IH in hv. destruct hv as [hl hall].
      split; [simpl; lia|]. intros b [e|hb]; [subst b; exact ha|apply hall; exact hb].
    + intros [hl hall]. destruct w as [|a v]; [discriminate|].
      exists a. split; [apply hall; left; reflexivity|].
      exists v. split; [|reflexivity]. apply IH. split.
      * simpl in hl. lia.
      * intros b hb. apply hall. right. exact hb.
Qed.

Lemma nodup_map_cons {A : Type} (a : A) (W : list (list A)) :
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

Lemma consAll_nodup {A : Type} (l : list A) (W : list (list A)) :
  NoDup l -> NoDup W -> NoDup (consAll l W).
Proof.
  induction l as [|a l IH]; intros hl hW; simpl; [constructor|].
  inversion hl as [|a' l' ha hl']; subst.
  apply nodup_app_intro; [apply nodup_map_cons; exact hW|apply IH; assumption|].
  intros x hx hy. apply in_map_iff in hx. destruct hx as (v & ev & _). subst x.
  apply mem_consAll in hy. destruct hy as (b & hb & u & _ & e).
  injection e as eab _. subst b. contradiction.
Qed.

(* Words over a duplicate-free alphabet are duplicate-free. *)
Theorem words_nodup {A : Type} (alph : list A) (s : nat) :
  NoDup alph -> NoDup (words alph s).
Proof.
  intro h. induction s as [|s IH]; simpl.
  - constructor; [intros []|constructor].
  - apply consAll_nodup; assumption.
Qed.

(* Truth tables. *)

Definition allBool (n : nat) : list (list bool) := words [false; true] n.

Theorem allBool_length (n : nat) : length (allBool n) = 2 ^ n.
Proof. unfold allBool. rewrite words_length. reflexivity. Qed.

Theorem allBool_nodup (n : nat) : NoDup (allBool n).
Proof.
  unfold allBool. apply words_nodup.
  constructor; [simpl; intros [h|[]]; discriminate|].
  constructor; [intros []|constructor].
Qed.

Theorem mem_allBool (n : nat) (x : list bool) : In x (allBool n) <-> length x = n.
Proof.
  unfold allBool. rewrite mem_words. split.
  - intros [h _]. exact h.
  - intro h. split; [exact h|]. intros [|] _; simpl; auto.
Qed.

(* Truth tables of n-bit functions: exactly 2 ^ (2 ^ n) of them. *)
Theorem tables_length (n : nat) : length (allBool (2 ^ n)) = 2 ^ (2 ^ n).
Proof. apply allBool_length. Qed.

(* The function whose truth table (in the order of allBool n) is tt. *)
Fixpoint fnOfTable (n : nat) (tt : list bool) (x : list bool) : bool :=
  match n with
  | 0 => hd false tt
  | S n' =>
    match x with
    | [] => false
    | b :: x' => fnOfTable n' (if b then skipn (2 ^ n') tt else firstn (2 ^ n') tt) x'
    end
  end.

Lemma allBool_succ (n : nat) :
  allBool (S n) = map (cons false) (allBool n) ++ map (cons true) (allBool n).
Proof. unfold allBool. simpl. rewrite app_nil_r. reflexivity. Qed.

(* Every table of length 2 ^ n is the truth table of a function. *)
Theorem table_of_fnOfTable (n : nat) (tt : list bool) :
  length tt = 2 ^ n -> map (fnOfTable n tt) (allBool n) = tt.
Proof.
  revert tt. induction n as [|n IH]; intros tt h.
  - destruct tt as [|b [|c t]]; simpl in h; try lia. reflexivity.
  - rewrite allBool_succ, map_app, !map_map.
    change (fun x => fnOfTable (S n) tt (false :: x)) with (fnOfTable n (firstn (2 ^ n) tt)).
    change (fun x => fnOfTable (S n) tt (true :: x)) with (fnOfTable n (skipn (2 ^ n) tt)).
    assert (ht : length (firstn (2 ^ n) tt) = 2 ^ n)
      by (rewrite length_firstn, h; simpl; lia).
    assert (hd : length (skipn (2 ^ n) tt) = 2 ^ n)
      by (rewrite length_skipn, h; simpl; lia).
    rewrite (IH _ ht), (IH _ hd). apply firstn_skipn.
Qed.

(* Pigeonhole. *)

(* A duplicate-free list covered by the image of codes is no longer than codes. *)
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

(* Abstract Shannon counting: fewer codes than truth tables leaves a table uncovered. *)
Theorem uncovered_table {Code : Type} (decode : Code -> list bool) (n : nat)
  (codes : list Code) :
  length codes < 2 ^ (2 ^ n) ->
  exists t, In t (allBool (2 ^ n)) /\ forall c, In c codes -> decode c <> t.
Proof.
  intro h.
  destruct (uncovered_or_cover decode codes (allBool (2 ^ n))) as [hu|hcov]; [exact hu|].
  pose proof (cover_length decode _ codes (allBool_nodup _) hcov) as hl.
  rewrite tables_length in hl. lia.
Qed.

(* Codes of length at most s over an alphabet, as one list. *)
Fixpoint codesUpTo {A : Type} (alph : list A) (s : nat) : list (list A) :=
  match s with
  | 0 => words alph 0
  | S s' => codesUpTo alph s' ++ words alph (S s')
  end.

Theorem codesUpTo_length {A : Type} (alph : list A) (s : nat) :
  1 <= length alph -> length (codesUpTo alph s) <= S s * length alph ^ s.
Proof.
  intro h1. induction s as [|s IH].
  - simpl. lia.
  - change (codesUpTo alph (S s)) with (codesUpTo alph s ++ words alph (S s)).
    rewrite length_app, words_length.
    assert (hp : length alph ^ s <= length alph ^ S s)
      by (apply Nat.pow_le_mono_r; lia).
    assert (hm : S s * length alph ^ s <= S s * length alph ^ S s)
      by (apply Nat.mul_le_mono_l; exact hp).
    remember (length alph ^ S s) as X.
    replace (S (S s) * X) with (X + S s * X) by (simpl; lia).
    lia.
Qed.

Theorem mem_codesUpTo {A : Type} (alph : list A) (s : nat) (w : list A) :
  length w <= s -> (forall a, In a w -> In a alph) -> In w (codesUpTo alph s).
Proof.
  intros hl ha. induction s as [|s IH].
  - change (codesUpTo alph 0) with (words alph 0). apply mem_words. split; [lia|exact ha].
  - change (codesUpTo alph (S s)) with (codesUpTo alph s ++ words alph (S s)).
    apply in_app_iff.
    destruct (Nat.le_gt_cases (length w) s) as [hs|hs].
    + left. apply IH. exact hs.
    + right. apply mem_words. split; [lia|exact ha].
Qed.

(* Shannon counting for any code-based description of functions. *)
Theorem shannon_codes {A : Type} (alph : list A) (decode : list A -> list bool) (n s : nat) :
  1 <= length alph ->
  S s * length alph ^ s < 2 ^ (2 ^ n) ->
  exists t, In t (allBool (2 ^ n)) /\
    forall w, length w <= s -> (forall a, In a w -> In a alph) -> decode w <> t.
Proof.
  intros h1 h.
  destruct (uncovered_table decode n (codesUpTo alph s)) as (t & ht & hno).
  - pose proof (codesUpTo_length alph s h1). lia.
  - exists t. split; [exact ht|]. intros w hl ha. apply hno. apply mem_codesUpTo; assumption.
Qed.

(* A concrete circuit model: NAND straight-line programs. *)

Definition Circuit := list (nat * nat).

Definition wire (w : list bool) (i : nat) : bool := nth i w false.

Fixpoint run (w : list bool) (C : Circuit) : list bool :=
  match C with
  | [] => w
  | (i, j) :: C' => run (w ++ [negb (wire w i && wire w j)]) C'
  end.

(* The output is the last wire. *)
Definition output (x : list bool) (C : Circuit) : bool := last (run x C) false.

(* Gate k only reads the n inputs and earlier gates. *)
Fixpoint WFfrom (N : nat) (C : Circuit) : Prop :=
  match C with
  | [] => True
  | (i, j) :: C' => i < N /\ j < N /\ WFfrom (S N) C'
  end.

Definition WF (n : nat) (C : Circuit) : Prop := WFfrom n C.

Fixpoint pairsOf (l m : list nat) : list (nat * nat) :=
  match l with
  | [] => []
  | a :: l' => map (fun b => (a, b)) m ++ pairsOf l' m
  end.

Lemma pairsOf_length (l m : list nat) : length (pairsOf l m) = length l * length m.
Proof.
  induction l as [|a l IH]; simpl; [reflexivity|].
  rewrite length_app, length_map, IH. reflexivity.
Qed.

Lemma mem_pairsOf (l m : list nat) (a b : nat) :
  In a l -> In b m -> In (a, b) (pairsOf l m).
Proof.
  induction l as [|c l IH]; intros ha hb; [destruct ha|]. simpl. apply in_app_iff.
  destruct ha as [e|ha].
  - subst c. left. apply in_map_iff. exists b. split; [reflexivity|exact hb].
  - right. apply IH; assumption.
Qed.

Lemma wf_bound (N : nat) (C : Circuit) :
  WFfrom N C -> forall p, In p C -> fst p < N + length C /\ snd p < N + length C.
Proof.
  revert N. induction C as [|[i j] C IH]; intros N h p hp; [destruct hp|].
  destruct h as (hi & hj & hC). simpl length.
  destruct hp as [e|hp].
  - subst p. simpl. lia.
  - destruct (IH (S N) hC p hp). lia.
Qed.

(* The gate alphabet for circuits with at most g gates on n inputs. *)
Definition gateAlphabet (n g : nat) : list (nat * nat) :=
  pairsOf (seq 0 (n + g)) (seq 0 (n + g)).

Lemma gateAlphabet_length (n g : nat) : length (gateAlphabet n g) = (n + g) * (n + g).
Proof. unfold gateAlphabet. rewrite pairsOf_length, length_seq. reflexivity. Qed.

Lemma wf_in_alphabet (n g : nat) (C : Circuit) :
  WF n C -> length C <= g -> forall p, In p C -> In p (gateAlphabet n g).
Proof.
  intros hw hl p hp. destruct (wf_bound n C hw p hp) as [h1 h2].
  destruct p as [i j]. simpl in h1, h2. unfold gateAlphabet.
  apply mem_pairsOf; apply in_seq; lia.
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

(* Shannon's counting theorem for NAND circuits. *)
Theorem shannon_circuits (n g : nat) :
  S g * ((n + g) * (n + g)) ^ g < 2 ^ (2 ^ n) ->
  exists f : list bool -> bool, forall C, WF n C -> length C <= g ->
    exists x, length x = n /\ output x C <> f x.
Proof.
  intro h.
  destruct (Nat.eq_dec (n + g) 0) as [h0|h0].
  - assert (hn : n = 0) by lia. assert (hg : g = 0) by lia. subst n g.
    exists (fun _ => true). intros C _ hl.
    destruct C as [|p C]; [|simpl in hl; lia].
    exists []. split; [reflexivity|]. unfold output. simpl. discriminate.
  - assert (h1 : 1 <= length (gateAlphabet n g)) by (rewrite gateAlphabet_length; nia).
    rewrite <- gateAlphabet_length in h.
    destruct (shannon_codes (gateAlphabet n g)
      (fun C => map (fun x => output x C) (allBool n)) n g h1 h) as (t & ht & hno).
    assert (htl : length t = 2 ^ n) by (apply mem_allBool in ht; exact ht).
    exists (fnOfTable n t). intros C hw hl.
    destruct (differ_or_agree (fun x => output x C) (fnOfTable n t) (allBool n))
      as [(x & hx & hne)|hall].
    + exists x. split; [apply mem_allBool; exact hx|exact hne].
    + exfalso. apply (hno C hl (wf_in_alphabet n g C hw hl)).
      rewrite <- (table_of_fnOfTable n t htl). apply map_ext_in. exact hall.
Qed.

(* Concrete instance: some Boolean function on 4 bits needs more than 2 NAND gates. *)
Theorem four_bit_function_needs_three_gates :
  exists f : list bool -> bool, forall C, WF 4 C -> length C <= 2 ->
    exists x, length x = 4 /\ output x C <> f x.
Proof.
  apply shannon_circuits. apply Nat.ltb_lt. vm_compute. reflexivity.
Qed.

(* The open obligation. *)

Record Poly := mkPoly { coefficient : nat; degree : nat }.

Definition eval (p : Poly) (n : nat) : nat := coefficient p * (n + 1) ^ degree p.

(* f has polynomial-size NAND circuits at every input length. *)
Definition PolySizeCircuits (f : list bool -> bool) : Prop :=
  exists p : Poly, forall n, exists C, WF n C /\ length C <= eval p n /\
    forall x, length x = n -> output x C = f x.

(* f has a superpolynomial circuit lower bound. *)
Definition SuperpolyLowerBound (f : list bool -> bool) : Prop :=
  forall p : Poly, exists n, forall C, WF n C -> length C <= eval p n ->
    exists x, length x = n /\ output x C <> f x.

(* The open obligation: an explicit function in InNP with a superpolynomial lower bound. *)
Definition ExplicitNPLowerBound (InNP : (list bool -> bool) -> Prop) : Prop :=
  exists f, InNP f /\ SuperpolyLowerBound f.

Theorem superpoly_excludes_poly_circuits (f : list bool -> bool) :
  SuperpolyLowerBound f -> ~ PolySizeCircuits f.
Proof.
  intros h (p & hp). destruct (h p) as (n & hn). destruct (hp n) as (C & hw & hl & hc).
  destruct (hn C hw hl) as (x & hx & hne). apply hne. apply hc. exact hx.
Qed.

(* Transfer to algorithms, given the simulation hypothesis. *)
Theorem no_fast_algorithm {Algorithm : Type} (computes : Algorithm -> list bool -> bool)
  (fast : Algorithm -> Prop)
  (simulation : forall a, fast a -> PolySizeCircuits (computes a))
  (f : list bool -> bool) :
  SuperpolyLowerBound f -> forall a, fast a -> computes a <> f.
Proof.
  intros h a ha e. apply (superpoly_excludes_poly_circuits f h).
  rewrite <- e. apply simulation. exact ha.
Qed.

(* Conditional separation from the obligation and the simulation hypothesis. *)
Theorem explicit_lower_bound_separates {Algorithm : Type}
  (InNP : (list bool -> bool) -> Prop) (computes : Algorithm -> list bool -> bool)
  (fast : Algorithm -> Prop)
  (simulation : forall a, fast a -> PolySizeCircuits (computes a)) :
  ExplicitNPLowerBound InNP -> exists f, InNP f /\ forall a, fast a -> computes a <> f.
Proof.
  intros (f & hf & hlb). exists f. split; [exact hf|].
  apply (no_fast_algorithm computes fast simulation f hlb).
Qed.
