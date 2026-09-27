(* Issue #532, Idea 26: separator consistency.

   Verdict: refuted as a route (general theorem): separator decomposition is
   exact only when all 2^|S| separator states are tracked, and no summary
   with fewer states is sound in general.

   Same content as ../lean/Idea26.lean:
   - separator_sat_iff: A ++ B (shared variables inside S) is satisfiable iff
     some state sigma in allBool |S| is realised by a model of A and by a
     model of B;
   - length_allBool / mem_allBool: 2^n states, all vectors of length n;
   - separate_not_joint: [[x]] and [[~x]] separately but not jointly SAT;
   - compatible_states_units / equality_gadget: unit formulas force exactly
     one separator state; the union is SAT iff the states are equal;
   - summary_must_be_injective: a sound summary distinguishes all states.

   Machine model (Machines.v): SepTree r phi is a recursive separator
   decomposition of phi with a total separator budget r along every branch,
   and SepPromise k w asks for it with r = k * log2 (|w|+1).  The named known
   theorem LogSeparatorSATInP (separator-state dynamic programming is
   polynomial on that promise) is used only as an explicit premise.  The open
   obligation SATSeparatorReduction asks for a Machine mapping every SAT
   instance, within a polynomial number of steps, to an equisatisfiable
   instance with such a decomposition; pEqualsNP_of_separatorReduction
   derives PEqualsNP from it, and not_forall_separatorReduction is the
   non-vacuity check.

   Differences from Lean: the Lean schema SeparatorObligationFor uses the
   projections (f phi).1, (f phi).2.1, (f phi).2.2; here the triple is
   destructured with let '(A, B, Sep) := f phi (same meaning).  The Lean
   viaMachine M m is noncomputable; here viaMachine M (m, p) is computable
   (it runs m for p(|x|) steps with the interpreter runOut and reads the
   output off the tape), viaMachine_eq holds pointwise, and
   exists_not_reducible diagonalises pointwise against (machine, polynomial)
   pairs, without function extensionality or excluded middle.  No axioms are
   used.
   See ../ideas/Idea26.md. *)

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

(* Separator states *)

Fixpoint allBool (n : nat) : list (list bool) :=
  match n with
  | 0 => [[]]
  | S n' => map (cons false) (allBool n') ++ map (cons true) (allBool n')
  end.

Theorem length_allBool : forall n, length (allBool n) = 2 ^ n.
Proof.
  induction n as [|n IH]; simpl.
  - reflexivity.
  - rewrite length_app, !length_map, IH; lia.
Qed.

Theorem mem_allBool : forall n (sigma : list bool),
  In sigma (allBool n) <-> length sigma = n.
Proof.
  induction n as [|n IH]; intros sigma; simpl.
  - split.
    + intros [H | []]; subst; reflexivity.
    + destruct sigma; simpl; [intros _; left; reflexivity | discriminate].
  - rewrite in_app_iff, !in_map_iff; split.
    + intros [[t [Ht Hin]] | [t [Ht Hin]]]; subst; simpl; f_equal; apply IH; exact Hin.
    + destruct sigma as [|b sigma]; simpl; [discriminate |].
      intros Hlen; injection Hlen as Hlen.
      destruct b; [right | left]; exists sigma; split; try reflexivity; apply IH; exact Hlen.
Qed.

Definition restrict (S : list nat) (a : Assignment) : list bool := map a S.

Lemma restrict_length : forall S a, length (restrict S a) = length S.
Proof. intros; unfold restrict; apply length_map. Qed.

Lemma restrict_eq_agree : forall S (a b : Assignment),
  restrict S a = restrict S b -> forall v, In v S -> a v = b v.
Proof.
  unfold restrict; induction S as [|s S IH]; intros a b H v Hv; simpl in *.
  - contradiction.
  - injection H as H1 H2. destruct Hv as [Hv | Hv].
    + subst; exact H1.
    + exact (IH a b H2 v Hv).
Qed.

(* Separator theorem. *)
Theorem separator_sat_iff : forall (A B : CNF) (S : list nat),
  (forall v, In v (vars A) -> In v (vars B) -> In v S) ->
  (Satisfiable (A ++ B) <->
   exists sigma, In sigma (allBool (length S)) /\
     (exists a, restrict S a = sigma /\ evalCNF a A = true) /\
     (exists b, restrict S b = sigma /\ evalCNF b B = true)).
Proof.
  intros A B S HS; split.
  - intros [a Ha]; rewrite evalCNF_append in Ha; apply andb_prop in Ha.
    destruct Ha as [HA HB].
    exists (restrict S a); split.
    + apply mem_allBool, restrict_length.
    + split; exists a; split; auto.
  - intros [sigma [_ [[a [Has Ha]] [b [Hbs Hb]]]]].
    assert (agree : forall v, In v S -> a v = b v).
    { apply restrict_eq_agree; rewrite Has, Hbs; reflexivity. }
    set (c := fun v => if in_dec Nat.eq_dec v (vars A) then a v else b v).
    exists c; rewrite evalCNF_append.
    assert (HcA : evalCNF c A = evalCNF a A).
    { apply eval_congr; intros v Hv; unfold c.
      destruct (in_dec Nat.eq_dec v (vars A)); [reflexivity | contradiction]. }
    assert (HcB : evalCNF c B = evalCNF b B).
    { apply eval_congr; intros v Hv; unfold c.
      destruct (in_dec Nat.eq_dec v (vars A)) as [HvA|HvA].
      - apply agree, HS; assumption.
      - reflexivity. }
    rewrite HcA, HcB, Ha, Hb; reflexivity.
Qed.

(* Countermodel family, |S| = 1. *)
Theorem separate_not_joint : forall x : nat,
  Satisfiable [[mkLit x true]] /\ Satisfiable [[mkLit x false]] /\
  ~ Satisfiable ([[mkLit x true]] ++ [[mkLit x false]]).
Proof.
  intros x; split; [exists (fun _ => true); reflexivity |].
  split; [exists (fun _ => false); reflexivity |].
  intros [a Ha]; simpl in Ha; unfold evalLit in Ha; simpl in Ha.
  destruct (a x); discriminate.
Qed.

(* The equality gadget *)

Fixpoint units (S : list nat) (sigma : list bool) : CNF :=
  match S, sigma with
  | s :: S', b :: sigma' => [mkLit s b] :: units S' sigma'
  | _, _ => []
  end.

Lemma evalLit_unit : forall (a : Assignment) s b,
  evalLit a (mkLit s b) = true <-> a s = b.
Proof.
  intros a s b; unfold evalLit; simpl.
  destruct b, (a s); simpl; split; intros H; try reflexivity; discriminate.
Qed.

Lemma units_eval : forall (a : Assignment) S (sigma : list bool),
  length sigma = length S ->
  (evalCNF a (units S sigma) = true <-> restrict S a = sigma).
Proof.
  intros a S; unfold restrict; induction S as [|s S IH]; intros sigma Hlen;
    destruct sigma as [|b sigma]; simpl in *; try discriminate.
  - split; reflexivity.
  - injection Hlen as Hlen.
    rewrite orb_false_r; split.
    + intros H; apply andb_prop in H; destruct H as [H1 H2].
      apply evalLit_unit in H1; apply (IH sigma Hlen) in H2.
      rewrite H1, H2; reflexivity.
    + intros H; injection H as H1 H2.
      apply andb_true_intro; split.
      * apply evalLit_unit; exact H1.
      * apply (IH sigma Hlen); exact H2.
Qed.

Theorem realizable : forall S, NoDup S -> forall sigma : list bool,
  length sigma = length S -> exists a, restrict S a = sigma.
Proof.
  unfold restrict; induction S as [|s S IH]; intros HS sigma Hlen;
    destruct sigma as [|b sigma]; simpl in *; try discriminate.
  - exists (fun _ => false); reflexivity.
  - injection Hlen as Hlen.
    inversion HS as [|s' S' Hs HS']; subst.
    destruct (IH HS' sigma Hlen) as [a Ha].
    exists (fun v => if Nat.eq_dec v s then b else a v).
    destruct (Nat.eq_dec s s) as [_|Hne]; [| contradiction].
    f_equal. rewrite <- Ha. apply map_ext_in. intros v Hv.
    destruct (Nat.eq_dec v s) as [Heq|_]; [subst; contradiction | reflexivity].
Qed.

(* Compatibility sets are singletons. *)
Theorem compatible_states_units : forall S, NoDup S -> forall sigma tau : list bool,
  length sigma = length S ->
  ((exists a, restrict S a = tau /\ evalCNF a (units S sigma) = true) <-> tau = sigma).
Proof.
  intros S HS sigma tau Hs; split.
  - intros [a [Hat Ha]]; rewrite <- Hat; apply (units_eval a S sigma Hs); exact Ha.
  - intros H; subst tau.
    destruct (realizable S HS sigma Hs) as [a Ha].
    exists a; split; [exact Ha | apply (units_eval a S sigma Hs); exact Ha].
Qed.

(* Equality gadget. *)
Theorem equality_gadget : forall S, NoDup S -> forall sigma tau : list bool,
  length sigma = length S -> length tau = length S ->
  Satisfiable (units S sigma) /\ Satisfiable (units S tau) /\
  (Satisfiable (units S sigma ++ units S tau) <-> sigma = tau).
Proof.
  intros S HS sigma tau Hs Ht; split; [| split].
  - destruct (realizable S HS sigma Hs) as [a Ha].
    exists a; apply (units_eval a S sigma Hs); exact Ha.
  - destruct (realizable S HS tau Ht) as [a Ha].
    exists a; apply (units_eval a S tau Ht); exact Ha.
  - split.
    + intros [a Ha]; rewrite evalCNF_append in Ha; apply andb_prop in Ha.
      destruct Ha as [H1 H2].
      apply (units_eval a S sigma Hs) in H1; apply (units_eval a S tau Ht) in H2.
      rewrite <- H1, <- H2; reflexivity.
    + intros H; subst tau.
      destruct (realizable S HS sigma Hs) as [a Ha].
      exists a; rewrite evalCNF_append.
      assert (E : evalCNF a (units S sigma) = true) by (apply (units_eval a S sigma Hs); exact Ha).
      rewrite E; reflexivity.
Qed.

(* No lossy summary. *)
Theorem summary_must_be_injective : forall (beta : Type) S, NoDup S ->
  forall (summ : list bool -> beta) (D : beta -> list bool -> bool),
  (forall sigma tau, length sigma = length S -> length tau = length S ->
     (D (summ sigma) tau = true <-> Satisfiable (units S sigma ++ units S tau))) ->
  forall sigma tau, length sigma = length S -> length tau = length S ->
  summ sigma = summ tau -> sigma = tau.
Proof.
  intros beta S HS summ D HD sigma tau Hs Ht Hsum.
  assert (H1 : D (summ sigma) sigma = true).
  { apply (HD sigma sigma Hs Hs).
    apply (equality_gadget S HS sigma sigma Hs Hs); reflexivity. }
  rewrite Hsum in H1.
  apply (HD tau sigma Ht Hs) in H1.
  apply (equality_gadget S HS tau sigma Ht Hs) in H1.
  symmetry; exact H1.
Qed.

(** Schema for (Sep), one level, over a caller-supplied class PolyTime of
    maps and a bound w: a map in PolyTime sending every CNF to an
    equisatisfiable split A ++ B whose shared variables lie in a separator Sep
    (a list of variables) of length at most w |phi|.  PolyTime is a free
    parameter, so the schema carries no running-time content; the machine
    version is SATSeparatorReduction below. *)
Definition SeparatorObligationFor (PolyTime : (CNF -> CNF * CNF * list nat) -> Prop)
  (w : nat -> nat) : Prop :=
  exists f : CNF -> CNF * CNF * list nat, PolyTime f /\ forall phi,
    let '(A, B, Sep) := f phi in
    (forall v, In v (vars A) -> In v (vars B) -> In v Sep) /\
    length Sep <= w (length phi) /\
    (Satisfiable phi <-> Satisfiable (A ++ B)).

(* Conditional theorem: under the schema, satisfiability of every CNF is
   decided by the 2 ^ w(|phi|) separator states. *)
Theorem separator_obligation_states (PolyTime : (CNF -> CNF * CNF * list nat) -> Prop)
  (w : nat -> nat) :
  SeparatorObligationFor PolyTime w ->
  exists f : CNF -> CNF * CNF * list nat, PolyTime f /\ forall phi,
    let '(A, B, Sep) := f phi in
    length Sep <= w (length phi) /\
    (Satisfiable phi <-> exists sigma, In sigma (allBool (length Sep)) /\
      (exists a, restrict Sep a = sigma /\ evalCNF a A = true) /\
      (exists b, restrict Sep b = sigma /\ evalCNF b B = true)).
Proof.
  intros (f & hf & hall). exists f. split; [exact hf|]. intro phi.
  specialize (hall phi). destruct (f phi) as [[A B] Sep].
  destruct hall as (hSep & hw & hp). split; [exact hw|].
  rewrite hp. apply separator_sat_iff. exact hSep.
Qed.

(** ** Recursive separator decompositions *)

(** [SepTree r phi]: [phi] is either a leaf with at most [r] variable
    occurrences, or a concatenation [A ++ B] whose shared variables lie in a
    separator [Sep] with [|Sep| <= r], both halves decomposed recursively with
    the remaining budget [r - |Sep|].  Along every branch the separators add up
    to at most [r], so the primal graph has treewidth below [2r]. *)
Inductive SepTree : nat -> CNF -> Prop :=
  | SepTree_leaf : forall (r : nat) (phi : CNF), length (vars phi) <= r -> SepTree r phi
  | SepTree_split : forall (r : nat) (A B : CNF) (Sep : list nat),
      (forall v, In v (vars A) -> In v (vars B) -> In v Sep) -> length Sep <= r ->
      SepTree (r - length Sep) A -> SepTree (r - length Sep) B -> SepTree r (A ++ B).

(** A separator tree exposes, at its root, either a small leaf or one exact
    separator step with at most [2^r] states ([separator_sat_iff]). *)
Theorem sepTree_root : forall r phi, SepTree r phi ->
  length (vars phi) <= r \/
    exists (A B : CNF) (Sep : list nat), phi = A ++ B /\ length Sep <= r /\
      (Satisfiable phi <-> exists sigma, In sigma (allBool (length Sep)) /\
        (exists a, restrict Sep a = sigma /\ evalCNF a A = true) /\
        (exists b, restrict Sep b = sigma /\ evalCNF b B = true)).
Proof.
  intros r phi h. destruct h as [r phi hl | r A B Sep hSep hlen _ _].
  - left. exact hl.
  - right. exists A, B, Sep. split; [reflexivity |]. split; [exact hlen |].
    apply separator_sat_iff. exact hSep.
Qed.

(** A separator tree with budget [r] also has every larger budget. *)
Theorem sepTree_mono : forall r phi, SepTree r phi -> forall r', r <= r' -> SepTree r' phi.
Proof.
  intros r phi h. induction h as [r phi hl | r A B Sep hSep hlen hA IHA hB IHB];
    intros r' hr.
  - apply SepTree_leaf. lia.
  - apply (SepTree_split r' A B Sep); [exact hSep | lia | apply IHA; lia | apply IHB; lia].
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

(** The shared language SAT is satisfiability in this file's syntax. *)
Theorem sat_ofM : forall w : Word, SAT w = true <-> Satisfiable (ofM (decode w)).
Proof.
  intro w. rewrite sat_iff. split; intros [a ha]; exists a.
  - rewrite evalCNF_ofM. exact ha.
  - rewrite <- evalCNF_ofM. exact ha.
Qed.

(** The word [w] encodes a CNF with a separator tree of budget
    [k * log2 (|w|+1)] (logarithmic treewidth). *)
Definition SepPromise (k : nat) (w : Word) : Prop :=
  SepTree (k * Nat.log2 (length w + 1)) (ofM (decode w)).

(** Known theorem, not mechanised here.  For each fixed k, SAT is decided in
    polynomial time on the promise SepPromise k.  The promise gives primal
    treewidth below 2k * log2 (|w|+1) (see SepTree); a tree decomposition of
    width O(k log |w|) is found in time 2^(O(k log |w|)) * poly = poly
    (Robertson-Seymour, Graph Minors XIII, JCTB 63, 1995; Bodlaender, Drange,
    Dregi, Fomin, Lokshtanov, Pilipczuk, SIAM J. Comput. 45(2), 2016), and
    dynamic programming over the separator states of the bags decides
    satisfiability in time 2^(O(tw)) * poly (Alekhnovich-Razborov, FOCS 2002;
    Samer-Szeider, J. Discrete Algorithms 8(1), 2010).  What is not mechanised
    is the Machine carrying this out.  Used only as an explicit premise. *)
Definition LogSeparatorSATInP : Prop :=
  forall k, exists (d : Machine) (p : Polynomial), DecidesOn d p (SepPromise k) SAT.

(** A polynomial-time machine reduction of [L] to SAT instances with a
    logarithmic separator tree. *)
Definition SeparatorReduction (L : Language) (k : nat) : Prop :=
  exists (m : Machine) (f : Word -> Word) (p : Polynomial), Computes m f p /\
    forall x, SepPromise k (f x) /\ L x = SAT (f x).

(** Open obligation ((Sep) with recursion, in the machine model).  For some k,
    a Machine maps every word x, within a polynomial number of Run steps, to a
    word f x with SAT x = SAT (f x) whose CNF has a separator tree with budget
    k * log2 (|f x|+1). *)
Definition SATSeparatorReduction : Prop := exists k, SeparatorReduction SAT k.

(** Transfer: a separator reduction and the separator-state decider put [L] in
    P. *)
Theorem inP_of_separatorReduction : forall (L : Language) (k : nat),
  LogSeparatorSATInP -> SeparatorReduction L k -> InP L.
Proof.
  intros L k hS [m [f [p [hm hf]]]].
  destruct (hS k) as [d [p' hd]].
  exact (inP_of_promise_reduction L SAT (SepPromise k) m d f p p' hm
    (fun x => proj1 (hf x)) (fun x => proj2 (hf x)) hd).
Qed.

(** Conditional theorem.  The open obligation and the known separator-state
    decider put SAT in P. *)
Theorem inP_sat_of_separatorReduction :
  LogSeparatorSATInP -> SATSeparatorReduction -> InP SAT.
Proof.
  intros hS [k hk]. exact (inP_of_separatorReduction SAT k hS hk).
Qed.

(** Conditional theorem.  With the hardness half of Cook-Levin, the open
    obligation gives P = NP. *)
Theorem pEqualsNP_of_separatorReduction :
  SATHard -> LogSeparatorSATInP -> SATSeparatorReduction -> PEqualsNP.
Proof.
  intros hard hS h. exact (pEqualsNP_of_inP_sat hard (inP_sat_of_separatorReduction hS h)).
Qed.

(** Machine analogue of separator_obligation_states: under the obligation,
    every reduced instance is a small leaf or splits exactly over at most
    2^(k log2 (|f x|+1)) separator states, and SAT x is its
    satisfiability. *)
Theorem separatorReduction_states : SATSeparatorReduction ->
  exists (k : nat) (m : Machine) (f : Word -> Word) (p : Polynomial), Computes m f p /\
    forall x, (SAT x = true <-> Satisfiable (ofM (decode (f x)))) /\
      (length (vars (ofM (decode (f x)))) <= k * Nat.log2 (length (f x) + 1) \/
        exists (A B : CNF) (Sep : list nat), ofM (decode (f x)) = A ++ B /\
          length Sep <= k * Nat.log2 (length (f x) + 1) /\
          (Satisfiable (A ++ B) <-> exists sigma, In sigma (allBool (length Sep)) /\
            (exists a, restrict Sep a = sigma /\ evalCNF a A = true) /\
            (exists b, restrict Sep b = sigma /\ evalCNF b B = true))).
Proof.
  intros [k [m [f [p [hm hf]]]]].
  exists k, m, f, p. split; [exact hm |]. intro x.
  split; [rewrite (proj2 (hf x)); apply sat_ofM |].
  destruct (sepTree_root _ _ (proj1 (hf x))) as [hl | [A [B [Sep [he [hl hs]]]]]].
  - left. exact hl.
  - right. exists A, B, Sep. split; [exact he |]. split; [exact hl |].
    rewrite <- he. exact hs.
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


(** Non-vacuity.  For every k, some language has no separator reduction, so
    [SeparatorReduction SAT k] is a statement about SAT. *)
Theorem not_forall_separatorReduction : forall k : nat,
  ~ (forall L : Language, SeparatorReduction L k).
Proof.
  intros k h.
  destruct (exists_not_reducible SAT) as [L hL].
  destruct (h L) as [m [f [p [hm hf]]]].
  destruct (hL m f p hm) as [x hx].
  exact (hx (proj2 (hf x))).
Qed.
