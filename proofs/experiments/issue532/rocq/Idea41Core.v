(** * Issue #532, Idea 41: Williams' algorithmic method in the shared model

    Rocq twin of [proofs/experiments/issue532/lean/Idea41Core.lean]; declaration
    names are aligned with the Lean namespace [Issue532.Idea41].

    Williams (2010, 2011) turned faster-than-exhaustive-search satisfiability
    algorithms into circuit lower bounds: if the satisfiability of circuits
    from a class [C] with [n] inputs and polynomially many gates can be
    decided in time [2^n / n^{omega(1)}], then NEXP is not contained in [C].
    For general circuits (P/poly) the algorithm is an open problem.

    - [InNTIME], [InNEXP], [NEXPSubsetPPoly]: nondeterministic time with [Run]
      step counts and paired certificates (clocked, as in [Complexity.ClassNP];
      [inNTIME_iff_idea16] shows it is Idea 16's class), the class NEXP, and
      the statement "NEXP is contained in P/poly" over [Circuits.v].
    - [CircuitSAT], [encCircuit], [bruteCircuitSAT_correct],
      [length_allAssignments]: circuit satisfiability as a language, and the
      exhaustive-search baseline with its [2^n] assignments.
    - [FastCircuitSAT]: the open obligation.  One machine decides
      satisfiability of circuits with [n] inputs and [(n+1)^k] gates within
      [2^n / n^{omega(1)}] [Run] steps.
    - [NTimeHierarchy], [EasyWitnessLemma], [WilliamsSpeedup]: the three
      known theorems of the proof, stated in the model and used only as
      explicit premises (never proved or assumed globally here).
    - [williams_method]: [FastCircuitSAT -> ~ NEXPSubsetPPoly] under those
      premises.  [williams_method_idea16] takes the hierarchy theorem in
      Idea 16's form ([nTimeHierarchy_of_idea16]), and
      [idea16_nTimeHierarchy_of_lazyDiagonal] reduces that form to the
      simulation statement below.
    - [lazy_diagonal], [nTimeHierarchy_of_lazyDiagonal]: the diagonal argument
      of Zak's hierarchy theorem, proved; what remains of [NTimeHierarchy] is
      the simulation statement [LazyDiagonalSimulation].
    - [fastCircuitSAT_of_pEqualsNP], [pNotEqualsNP_of_not_fastCircuitSAT],
      [pNotEqualsNP_of_nexpSubsetPPoly] in the public [Idea41] module: the
      obligation is implied by P = NP, so refuting it proves P <> NP.
    - [not_forall_inNTIME]: nondeterministic time classes are not everything.

    Differences from the Lean file (this file uses no axioms at all):
    - [CircuitSAT] is computable.  Lean defines it with a classical [decide]
      of "the word is [encCircuit n C] for a well-formed satisfiable [C]".
      Here a word is parsed by the decoder [decCircuit] (a left inverse of
      [encCircuit] that rejects trailing bits), well-formedness is checked by
      the Boolean [wfFromb] and satisfiability by exhaustive search
      [bruteCircuitSAT].  [circuitSAT_encode] has the Lean statement, and the
      new [circuitSAT_iff] shows that [CircuitSAT] is exactly the Lean
      language: [CircuitSAT w = true] iff
      [exists n C, w = encCircuit n C /\ WF n C /\ CircuitSatisfiable n C].
      The Lean file now also has an exact [decCircuit], [wfFromb], and a
      [verifyCircuit] certificate check. Both checks are proved equivalent
      to the shared language, while only Rocq's [CircuitSAT] itself is
      executable.
    - [acceptedLanguage] is computable.  Lean uses a classical [decide] of
      "some certificate of length at most [c * T n + c] is accepted within
      [c * T n + c] steps".  Here the certificates of bounded length are
      enumerated ([certsUpTo]) and each run is replayed with the step-bounded
      interpreter [runFor] of [Machines.v] ([acceptsWithinb]).
      [acceptedLanguage_spec] states the characterisation.
    - [eq_acceptedLanguage] is pointwise ([forall x, L x = acceptedLanguage m
      c T x]) instead of an equality of functions (no function
      extensionality).  For the same reason [not_forall_inNTIME] does not go
      through [exists_language_not_in_family] (which yields [F a <> L] for
      functions, while a verifier determines [L] only pointwise); it inlines
      the same Cantor diagonal over the encoding [encMachineConst] of
      (machine, constant) pairs, which is [encMachinePoly (m, c * (n+1)^0)]
      with the computable left inverse [decMachineConst] built from
      [decMachinePoly].  The statement is the Lean one.
    - [lazy_chain] takes the pointwise premise [forall x, L x = D x] instead
      of [L = D] (a weaker premise, so a stronger lemma); [lazy_diagonal] has
      the Lean statement [L <> D].
    - [wfFrom_bound] is [wf_bound] of [Circuits.v]; [succ_le_mul_two_pow_div]
      uses [le_two_pow_self] of [Circuits.v].
    - [List.take] is [firstn], [List.replicate] is [repeat], [List.any] is
      [existsb]. *)

From Stdlib Require Import Arith PeanoNat Lia Bool List.
Import ListNotations.
From proofs.experiments.issue532.rocq Require Import Machines Circuits.
From proofs.experiments.issue532.rocq Require Idea16.

(** ** Nondeterministic time *)

(** [m], started on [x] paired with the certificate [cert], accepts within
    [T] steps. *)
Definition AcceptsWithin (m : Machine) (T : nat) (x cert : Word) : Prop :=
  exists t, t <= T /\ Run m (pairedInput x cert) t true.

(** [m] is a clocked nondeterministic verifier for [L] with certificate
    length and running time at most [c * T(n) + c]: it halts within that
    bound on every short certificate, and [x] is in [L] iff it accepts one.
    The constant [c] absorbs constant factors and finitely many short
    inputs. *)
Definition VerifiesIn (m : Machine) (c : nat) (T : nat -> nat) (L : Language) : Prop :=
  (forall x cert, length cert <= c * T (length x) + c ->
     exists t b, t <= c * T (length x) + c /\ Run m (pairedInput x cert) t b) /\
  forall x : Word, L x = true <->
    exists cert : Word, length cert <= c * T (length x) + c /\
      AcceptsWithin m (c * T (length x) + c) x cert.

(** The class [NTIME(T)] over [Complexity.Machine]. *)
Definition InNTIME (T : nat -> nat) (L : Language) : Prop :=
  exists (m : Machine) (c : nat), VerifiesIn m c T L.

(** This is Idea 16's [NTIME(T)], the class its hierarchy theorem is stated
    for; so the two files use one definition. *)
Theorem inNTIME_iff_idea16 : forall (T : nat -> nat) (L : Language),
  InNTIME T L <-> Idea16.InNTIME T L.
Proof.
  intros T L. split.
  - intros [m [c [hhalt hL]]]. exists m, c. split; [exact hhalt |].
    intro x. rewrite (hL x). split.
    + intros [cert [hc [t [ht hr]]]]. exists cert, t. auto.
    + intros [cert [t [hc [ht hr]]]]. exists cert. split; [exact hc |]. exists t. auto.
  - intros [m [c [hhalt hL]]]. exists m, c. split; [exact hhalt |].
    intro x. rewrite (hL x). split.
    + intros [cert [t [hc [ht hr]]]]. exists cert. split; [exact hc |]. exists t. auto.
    + intros [cert [hc [t [ht hr]]]]. exists cert, t. auto.
Qed.

(** The exponential time bound [2^(n^k)]. *)
Definition expBound (k : nat) (n : nat) : nat := 2 ^ (n ^ k).

(** The class NEXP. *)
Definition InNEXP (L : Language) : Prop := exists k, InNTIME (expBound k) L.

(** The statement "NEXP is contained in P/poly" for NAND circuits. *)
Definition NEXPSubsetPPoly : Prop := forall L : Language, InNEXP L -> InPPoly L.

(** [NTIME(2^n)] is contained in NEXP. *)
Theorem inNEXP_of_inNTIME_two_pow : forall L : Language,
  InNTIME (fun n => 2 ^ n) L -> InNEXP L.
Proof.
  intros L [m [c [hhalt hm]]]. exists 1, m, c.
  assert (e : forall n, expBound 1 n = 2 ^ n) by (intro n; unfold expBound; rewrite Nat.pow_1_r; reflexivity).
  split.
  - intros x cert. rewrite e. exact (hhalt x cert).
  - intro x. rewrite e. exact (hm x).
Qed.

(** *** Non-vacuity

    A time class is a family of languages indexed by a machine and a
    constant, so Cantor's argument leaves a language outside it. *)

(** Boolean test of acceptance within [T] steps, by the step-bounded
    interpreter. *)
Definition acceptsWithinb (m : Machine) (T : nat) (x cert : Word) : bool :=
  match runFor m (pairedInput x cert) T with
  | Some true => true
  | _ => false
  end.

Lemma acceptsWithinb_iff : forall m T x cert,
  acceptsWithinb m T x cert = true <-> AcceptsWithin m T x cert.
Proof.
  intros m T x cert. unfold acceptsWithinb, AcceptsWithin. split.
  - destruct (runFor m (pairedInput x cert) T) as [[|] |] eqn:h; intro hb;
      try discriminate.
    exact (run_of_runFor _ _ _ _ h).
  - intros [t [ht hr]]. rewrite (runFor_of_run _ _ _ _ hr _ ht). reflexivity.
Qed.

(** All words of length at most [B]. *)
Definition certsUpTo (B : nat) : list Word := flat_map allAssignments (seq 0 (S B)).

Lemma mem_certsUpTo : forall B cert, In cert (certsUpTo B) <-> length cert <= B.
Proof.
  intros B cert. unfold certsUpTo. rewrite in_flat_map. split.
  - intros [n [hn hc]]. apply in_seq in hn. apply mem_allAssignments_iff in hc. lia.
  - intro h. exists (length cert). split.
    + apply in_seq. lia.
    + apply mem_allAssignments_iff. reflexivity.
Qed.

(** The language accepted by [m] with constant [c]. *)
Definition acceptedLanguage (m : Machine) (c : nat) (T : nat -> nat) : Language :=
  fun x => existsb (acceptsWithinb m (c * T (length x) + c) x)
                   (certsUpTo (c * T (length x) + c)).

Theorem acceptedLanguage_spec : forall m c T x,
  acceptedLanguage m c T x = true <->
    exists cert : Word, length cert <= c * T (length x) + c /\
      AcceptsWithin m (c * T (length x) + c) x cert.
Proof.
  intros m c T x. unfold acceptedLanguage. rewrite existsb_exists. split.
  - intros [cert [hin ha]]. exists cert. split.
    + apply mem_certsUpTo. exact hin.
    + apply acceptsWithinb_iff. exact ha.
  - intros [cert [hl ha]]. exists cert. split.
    + apply mem_certsUpTo. exact hl.
    + apply acceptsWithinb_iff. exact ha.
Qed.

Theorem eq_acceptedLanguage : forall m c T L,
  VerifiesIn m c T L -> forall x, L x = acceptedLanguage m c T x.
Proof.
  intros m c T L [_ h] x. pose proof (h x) as hx. pose proof (acceptedLanguage_spec m c T x) as ha.
  destruct (L x), (acceptedLanguage m c T x); try reflexivity.
  - symmetry. apply ha. apply hx. reflexivity.
  - apply hx. apply ha. reflexivity.
Qed.

(** (Machine, constant) pairs, encoded as a machine with the constant
    polynomial [c * (n+1)^0]. *)
Definition encMachineConst (x : Machine * nat) : Word :=
  encMachinePoly (fst x, {| coefficient := snd x; degree := 0 |}).

Definition decMachineConst (w : Word) : option (Machine * nat) :=
  obind (decMachinePoly w) (fun '(m, p) => Some (m, coefficient p)).

Lemma decMachineConst_encMachineConst : forall x,
  decMachineConst (encMachineConst x) = Some x.
Proof.
  intros [m c]. unfold decMachineConst, encMachineConst.
  rewrite decMachinePoly_encMachinePoly. reflexivity.
Qed.

(** No time bound puts every language in [NTIME(T)]. *)
Theorem not_forall_inNTIME : forall T : nat -> nat, ~ (forall L : Language, InNTIME T L).
Proof.
  intros T hall.
  set (L := fun w => match decMachineConst w with
                     | Some (m, c) => negb (acceptedLanguage m c T w)
                     | None => true
                     end).
  destruct (hall L) as [m [c hm]].
  pose proof (eq_acceptedLanguage m c T L hm (encMachineConst (m, c))) as h.
  unfold L at 1 in h. rewrite decMachineConst_encMachineConst in h.
  destruct (acceptedLanguage m c T (encMachineConst (m, c))); discriminate.
Qed.

(** ** Circuit satisfiability as a language *)

(** A gate [(i, j)] as two unary numbers. *)
Definition encGate (g : nat * nat) : Word := encNat (fst g) ++ encNat (snd g).

Theorem encGate_prefixFree : PrefixFree encGate.
Proof.
  intros [i j] [i' j'] r s h. unfold encGate in h. simpl in h.
  rewrite <- !app_assoc in h.
  destruct (encNat_prefixFree _ _ _ _ h) as [h1 h'].
  destruct (encNat_prefixFree _ _ _ _ h') as [h2 h''].
  subst. auto.
Qed.

(** A circuit instance: the number of inputs, then the gate list. *)
Definition encCircuit (n : nat) (C : Circuit) : Word := encNat n ++ encList encGate C.

Theorem encCircuit_injective : forall n n' C C',
  encCircuit n C = encCircuit n' C' -> n = n' /\ C = C'.
Proof.
  intros n n' C C' h. unfold encCircuit in h.
  destruct (encNat_prefixFree _ _ _ _ h) as [hn h'].
  rewrite <- (app_nil_r (encList encGate C)), <- (app_nil_r (encList encGate C')) in h'.
  destruct (encList_prefixFree _ encGate_prefixFree _ _ _ _ h') as [hC _].
  auto.
Qed.

(** *** A computable decoder for circuit instances *)

Theorem decNat_sound : forall w n r, decNat w = Some (n, r) -> w = encNat n ++ r.
Proof.
  induction w as [| b w IH]; intros n r h; simpl in h; [discriminate |].
  destruct b.
  - destruct (decNat w) as [[n' r'] |] eqn:hw; simpl in h; [| discriminate].
    injection h as <- <-. simpl. f_equal. apply IH. reflexivity.
  - injection h as <- <-. reflexivity.
Qed.

Definition decGate (w : Word) : option ((nat * nat) * Word) :=
  obind (decNat w) (fun '(i, r1) =>
  obind (decNat r1) (fun '(j, r2) => Some ((i, j), r2))).

Lemma decGate_encGate : forall g r, decGate (encGate g ++ r) = Some (g, r).
Proof.
  intros [i j] r. unfold decGate, encGate. simpl.
  rewrite <- app_assoc, decNat_encNat. simpl. rewrite decNat_encNat. reflexivity.
Qed.

Lemma decGate_sound : forall w g r, decGate w = Some (g, r) -> w = encGate g ++ r.
Proof.
  intros w g r h. unfold decGate in h.
  destruct (decNat w) as [[i r1] |] eqn:h1; simpl in h; [| discriminate].
  destruct (decNat r1) as [[j r2] |] eqn:h2; simpl in h; [| discriminate].
  injection h as <- <-. unfold encGate. simpl.
  rewrite (decNat_sound _ _ _ h1), (decNat_sound _ _ _ h2), app_assoc. reflexivity.
Qed.

Lemma decListFuel_sound : forall {A : Type} (e : A -> Word) (d : Word -> option (A * Word)),
  (forall w a r, d w = Some (a, r) -> w = e a ++ r) ->
  forall fuel w l r, decListFuel d fuel w = Some (l, r) -> w = encList e l ++ r.
Proof.
  intros A e d hd fuel. induction fuel as [| fuel IH]; intros w l r h;
    simpl in h; [discriminate |].
  destruct w as [| [|] w]; [discriminate | |].
  - destruct (d w) as [[a r1] |] eqn:h1; simpl in h; [| discriminate].
    destruct (decListFuel d fuel r1) as [[l' r2] |] eqn:h2; simpl in h; [| discriminate].
    injection h as <- <-. simpl.
    rewrite (hd _ _ _ h1), (IH _ _ _ h2), app_assoc. reflexivity.
  - injection h as <- <-. reflexivity.
Qed.

(** Parse a circuit instance; trailing bits are rejected. *)
Definition decCircuit (w : Word) : option (nat * Circuit) :=
  obind (decNat w) (fun '(n, r) =>
  obind (decList decGate r) (fun '(C, r') =>
  match r' with [] => Some (n, C) | _ => None end)).

Lemma decCircuit_encCircuit : forall n C, decCircuit (encCircuit n C) = Some (n, C).
Proof.
  intros n C. unfold decCircuit, encCircuit. rewrite decNat_encNat. simpl.
  rewrite <- (app_nil_r (encList encGate C)).
  rewrite (decList_encList encGate decGate decGate_encGate). reflexivity.
Qed.

Lemma decCircuit_sound : forall w n C, decCircuit w = Some (n, C) -> w = encCircuit n C.
Proof.
  intros w n C h. unfold decCircuit in h.
  destruct (decNat w) as [[n' r] |] eqn:h1; simpl in h; [| discriminate].
  destruct (decList decGate r) as [[C' r'] |] eqn:h2; simpl in h; [| discriminate].
  destruct r'; [| discriminate]. injection h as <- <-.
  unfold decList in h2.
  pose proof (decListFuel_sound encGate decGate decGate_sound _ _ _ _ h2) as hr.
  rewrite app_nil_r in hr. unfold encCircuit. rewrite (decNat_sound _ _ _ h1), hr.
  reflexivity.
Qed.

(** Boolean well-formedness. *)
Fixpoint wfFromb (N : nat) (C : Circuit) : bool :=
  match C with
  | [] => true
  | (i, j) :: C' => (i <? N) && (j <? N) && wfFromb (N + 1) C'
  end.

Lemma wfFromb_iff : forall C N, wfFromb N C = true <-> WFfrom N C.
Proof.
  induction C as [| [i j] C IH]; intro N; simpl; [tauto |].
  rewrite !andb_true_iff, !Nat.ltb_lt, IH. tauto.
Qed.

(** Parse and check well-formedness, rejecting every malformed word. *)
Definition checkCircuit (w : Word) : bool :=
  match decCircuit w with
  | None => false
  | Some (n, C) => wfFromb n C
  end.

Theorem checkCircuit_iff : forall w,
  checkCircuit w = true <-> exists n C, w = encCircuit n C /\ WF n C.
Proof.
  intro w. unfold checkCircuit. destruct (decCircuit w) as [[n C]|] eqn:hd.
  - rewrite wfFromb_iff. split.
    + intro h. exists n, C. auto using decCircuit_sound.
    + intros [n' [C' [heq hwf]]].
      rewrite heq, decCircuit_encCircuit in hd. injection hd as <- <-.
      exact hwf.
  - split; [discriminate |].
    intros [n [C [heq _]]]. rewrite heq, decCircuit_encCircuit in hd. discriminate.
Qed.

(** Some input of length [n] makes [C] output [true]. *)
Definition CircuitSatisfiable (n : nat) (C : Circuit) : Prop :=
  exists x : Word, length x = n /\ output x C = true.

(** ** The exhaustive-search baseline *)

Theorem length_allAssignments : forall n, length (allAssignments n) = 2 ^ n.
Proof.
  induction n as [| n IH]; [reflexivity |].
  simpl. rewrite length_app, !length_map, IH. lia.
Qed.

(** Exhaustive search: evaluate [C] on all [2^n] inputs. *)
Definition bruteCircuitSAT (n : nat) (C : Circuit) : bool :=
  existsb (fun x => output x C) (allAssignments n).

Theorem bruteCircuitSAT_correct : forall n C,
  bruteCircuitSAT n C = true <-> CircuitSatisfiable n C.
Proof.
  intros n C. unfold bruteCircuitSAT, CircuitSatisfiable. rewrite existsb_exists.
  split.
  - intros [x [hx ho]]. exists x. split; [apply mem_allAssignments_iff; exact hx | exact ho].
  - intros [x [hx ho]]. exists x. split; [apply mem_allAssignments_iff; exact hx | exact ho].
Qed.

(** Exhaustive search evaluates [2^n] circuits of [|C|] gates each. *)
Definition bruteForceGateEvaluations (n : nat) (C : Circuit) : nat :=
  length (allAssignments n) * length C.

Theorem bruteForceGateEvaluations_eq : forall n C,
  bruteForceGateEvaluations n C = 2 ^ n * length C.
Proof. intros n C. unfold bruteForceGateEvaluations. rewrite length_allAssignments. reflexivity. Qed.

(** *** The language *)

(** Circuit satisfiability: the word encodes a well-formed satisfiable
    circuit.  Computable: parse, check well-formedness, search. *)
Definition CircuitSAT : Language := fun w =>
  match decCircuit w with
  | Some (n, C) => wfFromb n C && bruteCircuitSAT n C
  | None => false
  end.

Theorem circuitSAT_encode : forall n C,
  CircuitSAT (encCircuit n C) = true <-> WF n C /\ CircuitSatisfiable n C.
Proof.
  intros n C. unfold CircuitSAT. rewrite decCircuit_encCircuit.
  rewrite andb_true_iff, wfFromb_iff, bruteCircuitSAT_correct. reflexivity.
Qed.

(** [CircuitSAT] is the language of the Lean file. *)
Theorem circuitSAT_iff : forall w,
  CircuitSAT w = true <->
    exists n C, w = encCircuit n C /\ WF n C /\ CircuitSatisfiable n C.
Proof.
  intro w. split.
  - intro h. unfold CircuitSAT in h.
    destruct (decCircuit w) as [[n C] |] eqn:hd; [| discriminate].
    pose proof (decCircuit_sound _ _ _ hd) as hw.
    exists n, C. split; [exact hw |]. apply circuitSAT_encode. rewrite <- hw.
    unfold CircuitSAT. rewrite hd. exact h.
  - intros [n [C [-> h]]]. apply circuitSAT_encode. exact h.
Qed.

(** A finite certificate check using the exact decoder and the NAND evaluator.
    [CircuitVerifier] implements this function with a proved [Run] bound. *)
Definition verifyCircuit (w cert : Word) : bool :=
  match decCircuit w with
  | None => false
  | Some (n, C) => wfFromb n C && Nat.eqb (length cert) n && output cert C
  end.

Theorem verifyCircuit_spec : forall w cert,
  verifyCircuit w cert = true <->
    exists n C, decCircuit w = Some (n, C) /\ WF n C /\
      length cert = n /\ output cert C = true.
Proof.
  intros w cert. unfold verifyCircuit.
  destruct (decCircuit w) as [[n C]|] eqn:hd.
  - rewrite !andb_true_iff, Nat.eqb_eq, wfFromb_iff.
    split.
    + intros [[hwf hlen] hout]. exists n, C. auto.
    + intros [n' [C' [hdec [hwf [hlen hout]]]]].
      injection hdec as <- <-. auto.
  - split; [discriminate |].
    intros [n [C [hdec _]]]. discriminate.
Qed.

Theorem circuitSAT_iff_verifyCircuit : forall w,
  CircuitSAT w = true <-> exists cert, verifyCircuit w cert = true.
Proof.
  intro w. rewrite circuitSAT_iff. split.
  - intros [n [C [heq [hwf [cert [hlen hout]]]]]].
    exists cert. apply verifyCircuit_spec.
    exists n, C. rewrite heq. repeat split; auto using decCircuit_encCircuit.
  - intros [cert h]. apply verifyCircuit_spec in h.
    destruct h as [n [C [hd [hwf [hlen hout]]]]].
    exists n, C. repeat split; auto using decCircuit_sound.
    exists cert. auto.
Qed.

(** Each NAND gate extends the wire list by exactly one bit. *)
Theorem wires_length : forall (x : Word) (C : Circuit),
  length (wires x C) = length x + length C.
Proof.
  intros x C. revert x. induction C as [| [i j] C IH]; intro x; simpl; [lia |].
  rewrite IH, length_app. simpl. lia.
Qed.

(** Circuit satisfiability in NP; proved in the public [Idea41] module:
    the certificate is a satisfying input and the verifier evaluates the
    circuit (Karp 1972; Arora-Barak 6.1). [CircuitVerifier] proves its finite
    implementation and charged bound. *)
Definition CircuitSATInNP : Prop := InNP CircuitSAT.

(** ** The open obligation *)

(** Open obligation (Williams 2010).  For every [k] one [Machine] decides
    satisfiability of well-formed circuits with [n] inputs and at most
    [(n+1)^k] gates in [2^n / n^{omega(1)}] [Run] steps: for every [c], from
    some length on, [t * (n+1)^c <= 2^n].  Exhaustive search needs
    [2^n * |C|] gate evaluations ([bruteForceGateEvaluations_eq]). *)
Definition FastCircuitSAT : Prop :=
  forall k : nat, exists m : Machine, forall c : nat, exists n0 : nat,
    forall n : nat, n0 <= n ->
    forall C : Circuit, WF n C -> length C <= (n + 1) ^ k ->
      exists t b, t * (n + 1) ^ c <= 2 ^ n /\ Run m (initial (encCircuit n C)) t b /\
        (b = true <-> CircuitSatisfiable n C).

(** ** The known theorems of the proof *)

(** The truth table of a circuit on [l] inputs, as a word of length
    [2^l]. *)
Definition truthTable (l : nat) (W : Circuit) : Word :=
  map (fun y => output y W) (allAssignments l).

Theorem length_truthTable : forall l W, length (truthTable l W) = 2 ^ l.
Proof. intros l W. unfold truthTable. rewrite length_map, length_allAssignments. reflexivity. Qed.

(** Every NEXP verifier has succinct witnesses: every accepted input has an
    accepted certificate that is a prefix of the truth table of a circuit
    with polynomially many gates. *)
Definition SuccinctWitnesses : Prop :=
  forall (k : nat) (m : Machine) (c : nat) (L : Language), VerifiesIn m c (expBound k) L ->
    exists d : nat, forall x : Word, L x = true ->
      exists (l r : nat) (W : Circuit), length W <= d * (length x + 1) ^ d /\ WF l W /\
        r <= c * expBound k (length x) + c /\
        AcceptsWithin m (c * expBound k (length x) + c) x (firstn r (truthTable l W)).

(** Known theorem, not mechanised here: the easy-witness lemma
    (Impagliazzo-Kabanets-Wigderson 2002, Theorem 11; Williams 2013,
    Lemma 3.1).  If NEXP is contained in P/poly, every NEXP verifier has
    succinct witnesses. *)
Definition EasyWitnessLemma : Prop := NEXPSubsetPPoly -> SuccinctWitnesses.

(** Known theorem, not mechanised here: the nondeterministic time hierarchy
    (Cook 1973; Seiferas-Fischer-Meyer 1978; Zak 1983).  Some language in
    [NTIME(2^n)] is outside [NTIME(2^n / (n+1)^c)].
    [nTimeHierarchy_of_lazyDiagonal] proves the diagonal part. *)
Definition NTimeHierarchy : Prop :=
  exists (c : nat) (L : Language), InNTIME (fun n => 2 ^ n) L /\
    ~ InNTIME (fun n => 2 ^ n / (n + 1) ^ c) L.

(** Known theorem, not mechanised here: Williams' speedup (Williams 2010,
    Theorem 1.1 and section 3; Williams 2013).  A fast circuit-satisfiability
    algorithm and succinct witnesses put every language of [NTIME(2^n)] into
    [NTIME(2^n / (n+1)^c)] for every [c], through a quasi-linear Cook-Levin
    reduction to Succinct-3SAT (Tourlakis 2001;
    Fortnow-Lipton-van Melkebeek-Viglas 2005). *)
Definition WilliamsSpeedup : Prop :=
  FastCircuitSAT -> SuccinctWitnesses ->
    forall (c : nat) (L : Language), InNTIME (fun n => 2 ^ n) L ->
      InNTIME (fun n => 2 ^ n / (n + 1) ^ c) L.

(** ** The method *)

(** Williams' algorithmic method.  A fast circuit-satisfiability algorithm
    refutes "NEXP is contained in P/poly", given the three known theorems. *)
Theorem williams_method : NTimeHierarchy -> EasyWitnessLemma -> WilliamsSpeedup ->
  FastCircuitSAT -> ~ NEXPSubsetPPoly.
Proof.
  intros [c [L [hL hnot]]] ewl speedup fast hsub.
  exact (hnot (speedup fast (ewl hsub) c L hL)).
Qed.

(** The contrapositive. *)
Theorem not_fastCircuitSAT_of_nexpSubsetPPoly : NTimeHierarchy -> EasyWitnessLemma ->
  WilliamsSpeedup -> NEXPSubsetPPoly -> ~ FastCircuitSAT.
Proof.
  intros hier ewl speedup hsub fast. exact (williams_method hier ewl speedup fast hsub).
Qed.

(** Idea 16 states the hierarchy theorem for every gap [(n+1)^k] with
    [k >= 3]; the method needs one gap. *)
Theorem nTimeHierarchy_of_idea16 : Idea16.NTimeHierarchy -> NTimeHierarchy.
Proof.
  intro h. destruct (h 3 (le_n 3)) as [L [hL hnot]]. exists 3, L. split.
  - apply inNTIME_iff_idea16. exact hL.
  - intro h'. apply hnot. apply inNTIME_iff_idea16. exact h'.
Qed.

(** The method with Idea 16's form of the hierarchy theorem. *)
Theorem williams_method_idea16 : Idea16.NTimeHierarchy -> EasyWitnessLemma ->
  WilliamsSpeedup -> FastCircuitSAT -> ~ NEXPSubsetPPoly.
Proof.
  intros hier ewl speedup fast.
  exact (williams_method (nTimeHierarchy_of_idea16 hier) ewl speedup fast).
Qed.

(** ** Discharging the diagonal part of the hierarchy theorem

    Zak's lazy diagonalisation.  The diagonal language [D] copies [L] one
    step ahead on the unary inputs [1^l, ..., 1^(u-1)] and flips [L(1^l)] at
    [1^u]. *)

(** The unary word [1^n]. *)
Definition unary (n : nat) : Word := repeat true n.

Theorem lazy_chain : forall (D L : Language) (l j : nat),
  (forall n, l <= n -> n < l + j -> D (unary n) = L (unary (n + 1))) ->
  (forall x, L x = D x) -> D (unary l) = D (unary (l + j)).
Proof.
  intros D L l j. induction j as [| j IH]; intros hin heq.
  - rewrite Nat.add_0_r. reflexivity.
  - rewrite (IH (fun n h1 h2 => hin n h1 ltac:(lia)) heq).
    rewrite (hin (l + j)) by lia. rewrite heq.
    replace (l + j + 1) with (l + S j) by lia. reflexivity.
Qed.

(** Lazy diagonalisation (Zak 1983). *)
Theorem lazy_diagonal : forall (D L : Language) (l u : nat), l < u ->
  (forall n, l <= n -> n < u -> D (unary n) = L (unary (n + 1))) ->
  D (unary u) = negb (L (unary l)) -> L <> D.
Proof.
  intros D L l u hlu hin hend heq.
  assert (hpt : forall x, L x = D x) by (intro x; rewrite heq; reflexivity).
  pose proof (lazy_chain D L l (u - l) (fun n h1 h2 => hin n h1 ltac:(lia)) hpt) as hc.
  replace (l + (u - l)) with u in hc by lia.
  rewrite hend, hpt in hc. destruct (D (unary l)); discriminate.
Qed.

(** What remains of the hierarchy theorem: a language [D] in [NTIME(T)] that
    follows every language of [NTIME(T')] lazily on some interval. *)
Definition LazyDiagonalSimulation (T T' : nat -> nat) : Prop :=
  exists D : Language, InNTIME T D /\ forall L : Language, InNTIME T' L ->
    exists l u, l < u /\ (forall n, l <= n -> n < u -> D (unary n) = L (unary (n + 1))) /\
      D (unary u) = negb (L (unary l)).

Theorem not_inNTIME_of_lazyDiagonal : forall (T' : nat -> nat) (D : Language),
  (forall L : Language, InNTIME T' L ->
    exists l u, l < u /\ (forall n, l <= n -> n < u -> D (unary n) = L (unary (n + 1))) /\
      D (unary u) = negb (L (unary l))) -> ~ InNTIME T' D.
Proof.
  intros T' D hD h. destruct (hD D h) as [l [u [hlu [hin hend]]]].
  exact (lazy_diagonal D D l u hlu hin hend eq_refl).
Qed.

(** The hierarchy theorem from the simulation statement. *)
Theorem nTimeHierarchy_of_lazyDiagonal : forall c : nat,
  LazyDiagonalSimulation (fun n => 2 ^ n) (fun n => 2 ^ n / (n + 1) ^ c) ->
  NTimeHierarchy.
Proof.
  intros c [D [hD hlazy]]. exists c, D. split; [exact hD |].
  exact (not_inNTIME_of_lazyDiagonal _ D hlazy).
Qed.

(** The method with the hierarchy theorem replaced by the simulation
    statement. *)
Theorem williams_method_lazy : forall c : nat,
  LazyDiagonalSimulation (fun n => 2 ^ n) (fun n => 2 ^ n / (n + 1) ^ c) ->
  EasyWitnessLemma -> WilliamsSpeedup -> FastCircuitSAT -> ~ NEXPSubsetPPoly.
Proof.
  intros c sim ewl speedup fast.
  exact (williams_method (nTimeHierarchy_of_lazyDiagonal c sim) ewl speedup fast).
Qed.

(** Idea 16's form of the hierarchy theorem from the simulation statement,
    one gap [k >= 3] at a time: the diagonal argument is the same. *)
Theorem idea16_nTimeHierarchy_of_lazyDiagonal :
  (forall k, 3 <= k ->
     LazyDiagonalSimulation (fun n => 2 ^ n) (fun n => 2 ^ n / (n + 1) ^ k)) ->
  Idea16.NTimeHierarchy.
Proof.
  intros h k hk. destruct (h k hk) as [D [hD hlazy]]. exists D. split.
  - apply inNTIME_iff_idea16. exact hD.
  - intro h'. apply (not_inNTIME_of_lazyDiagonal _ D hlazy). apply inNTIME_iff_idea16. exact h'.
Qed.

(** ** The obligation and the separation question *)

(** [n + 1 <= r * 2^(n / r)]. *)
Theorem succ_le_mul_two_pow_div : forall r n, 0 < r -> n + 1 <= r * 2 ^ (n / r).
Proof.
  intros r n hr.
  pose proof (Nat.div_mod n r ltac:(lia)) as h1.
  pose proof (Nat.mod_upper_bound n r ltac:(lia)) as h2.
  pose proof (le_two_pow_self (n / r)) as h3.
  apply Nat.le_trans with (r * (n / r + 1)).
  - rewrite Nat.mul_add_distr_l, Nat.mul_1_r. lia.
  - apply Nat.mul_le_mono_l. exact h3.
Qed.

(** A polynomial is below [2^n] from some [n] on. *)
Theorem poly_le_two_pow : forall a e : nat,
  exists N, forall n, N <= n -> a * (n + 1) ^ e <= 2 ^ n.
Proof.
  intros a e. exists (2 * (a * (2 * e + 2) ^ e)). intros n hn.
  set (r := 2 * e + 2) in *. set (q := n / r).
  pose proof (Nat.div_mod n r ltac:(lia)) as hdm. fold q in hdm.
  pose proof (Nat.div_mod n 2 ltac:(lia)) as h2.
  pose proof (Nat.mod_upper_bound n 2 ltac:(lia)) as h2'.
  assert (hq : q * e <= n / 2).
  { apply Nat.div_le_lower_bound; [lia |].
    assert (r * q = 2 * (q * e) + 2 * q) by (unfold r; ring). lia. }
  assert (hK : a * r ^ e <= 2 ^ (n / 2)).
  { assert (a * r ^ e <= n / 2) by (apply Nat.div_le_lower_bound; lia).
    pose proof (le_two_pow_self (n / 2)). lia. }
  apply Nat.le_trans with (a * (r * 2 ^ q) ^ e).
  { apply Nat.mul_le_mono_l, Nat.pow_le_mono_l, succ_le_mul_two_pow_div. lia. }
  rewrite Nat.pow_mul_l, <- Nat.pow_mul_r, Nat.mul_assoc.
  apply Nat.le_trans with (2 ^ (n / 2) * 2 ^ (n / 2)).
  { apply Nat.mul_le_mono; [exact hK | apply Nat.pow_le_mono_r; lia]. }
  rewrite <- Nat.pow_add_r. apply Nat.pow_le_mono_r; lia.
Qed.

Theorem length_encNat : forall i, length (encNat i) = i + 1.
Proof. induction i as [| i IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

(** Parsed input and gate counts are bounded by the encoded word length. *)
Theorem decCircuit_data_bounds : forall w n C,
  decCircuit w = Some (n, C) ->
  n + 1 <= length w /\ length C + 1 <= length w.
Proof.
  intros w n C hd. pose proof (decCircuit_sound _ _ _ hd) as hw.
  pose proof (length_encList encGate C) as hc.
  rewrite hw. unfold encCircuit. rewrite length_app, length_encNat. lia.
Qed.

Theorem verifyCircuit_cert_bound : forall w cert,
  verifyCircuit w cert = true -> length cert <= length w.
Proof.
  intros w cert h. apply verifyCircuit_spec in h.
  destruct h as [n [C [hd [_ [hlen _]]]]].
  pose proof (decCircuit_data_bounds _ _ _ hd) as [hb _]. lia.
Qed.

(** This packages the NP record only. The explicit hypothesis still requires
    the full finite-machine evaluator and a polynomial bound on every bounded
    certificate, including malformed inputs. *)
Theorem circuitSATInNP_of_verifier_run : forall (m : Machine) (time : Polynomial),
  (forall x cert, length cert <= length x + 1 ->
    exists t, t <= evalPoly time (length x + length cert + 1) /\
      Run m (pairedInput x cert) t (verifyCircuit x cert)) -> CircuitSATInNP.
Proof.
  intros m time hrun.
  assert (hterm : forall x cert, length cert <= evalPoly
    {| coefficient := 1; degree := 1 |} (length x) ->
    exists t b, t <= timeLimit (paired m) time x cert /\
      verifierRun (paired m) x cert t b).
  { intros x cert hc. unfold evalPoly in hc. simpl in hc.
    destruct (hrun x cert ltac:(lia)) as [t [ht hr]].
    exists t, (verifyCircuit x cert). auto. }
  assert (hcorr : forall x, CircuitSAT x = true <->
    exists cert t, length cert <= evalPoly {| coefficient := 1; degree := 1 |} (length x) /\
      t <= timeLimit (paired m) time x cert /\ verifierRun (paired m) x cert t true).
  { intro x. rewrite circuitSAT_iff_verifyCircuit. split.
    - intros [cert hv]. pose proof (verifyCircuit_cert_bound x cert hv) as hc.
      destruct (hrun x cert ltac:(lia)) as [t [ht hr]].
      exists cert, t. rewrite hv in hr. repeat split; auto. unfold evalPoly. simpl. lia.
    - intros [cert [t [hc [_ hr]]]]. unfold evalPoly in hc. simpl in hc.
      destruct (hrun x cert ltac:(lia)) as [t' [_ hr']].
      exists cert. symmetry. exact (proj2 (run_deterministic _ _ _ _ _ _ hr hr')). }
  exists {| np_language := CircuitSAT; np_verifier := paired m; np_timeBound := time;
    np_certBound := {| coefficient := 1; degree := 1 |};
    np_terminates := hterm; np_correct := hcorr |}. reflexivity.
Qed.

(** In a well-formed circuit every gate reads a wire below [N + |C|]. *)
Theorem wfFrom_bound : forall (N : nat) (C : Circuit), WFfrom N C ->
  forall g, In g C -> fst g < N + length C /\ snd g < N + length C.
Proof. exact wf_bound. Qed.

Theorem length_encList_gates : forall (B : nat) (C : Circuit),
  (forall g, In g C -> fst g < B /\ snd g < B) ->
  length (encList encGate C) <= 1 + length C * (2 * B + 1).
Proof.
  intros B C. induction C as [| [i j] C IH]; intro h; simpl; [lia |].
  destruct (h (i, j) (or_introl eq_refl)) as [hi hj]. simpl in hi, hj.
  pose proof (IH (fun g hg => h g (or_intror hg))) as ih.
  rewrite length_app.
  assert (hg : length (encGate (i, j)) = i + 1 + (j + 1))
    by (unfold encGate; simpl; rewrite length_app, !length_encNat; reflexivity).
  rewrite hg. lia.
Qed.

(** A well-formed circuit with at most [(n+1)^k] gates has an encoding of
    polynomial length in [n]. *)
Theorem encCircuit_length_le : forall n k (C : Circuit), WF n C ->
  length C <= (n + 1) ^ k ->
  length (encCircuit n C) + 1 <= 8 * (n + 1) ^ (k + 1 + (k + 1)).
Proof.
  intros n k C hwf hs.
  pose proof (length_encList_gates (n + length C) C (wfFrom_bound n C hwf)) as hE.
  assert (hn1 : n + 1 <= (n + 1) ^ (k + 1)).
  { rewrite <- (Nat.pow_1_r (n + 1)) at 1. apply Nat.pow_le_mono_r; lia. }
  assert (hC1 : length C <= (n + 1) ^ (k + 1)).
  { apply Nat.le_trans with ((n + 1) ^ k); [exact hs |]. apply Nat.pow_le_mono_r; lia. }
  rewrite Nat.pow_add_r. unfold encCircuit. rewrite length_app, length_encNat.
  set (Q := (n + 1) ^ (k + 1)) in *. clearbody Q.
  assert (hm : length C * (2 * (n + length C) + 1) <= Q * (4 * Q + 1)).
  { apply Nat.mul_le_mono; lia. }
  nia.
Qed.

(** A polynomial-time decider for circuit satisfiability meets the
    obligation. *)
Theorem fastCircuitSAT_of_inP : InP CircuitSAT -> FastCircuitSAT.
Proof.
  intros h k. apply polyDec_iff_inP in h. destruct h as [m [p hm]].
  exists m. intro c.
  destruct (poly_le_two_pow (coefficient p * 8 ^ degree p)
              ((k + 1 + (k + 1)) * degree p + c)) as [N hN].
  exists N. intros n hn C hwf hsize.
  destruct (hm (encCircuit n C)) as [t [b [ht [hr hb]]]].
  exists t, b. split; [| split; [exact hr |]].
  - pose proof (encCircuit_length_le n k C hwf hsize) as hlen.
    unfold evalPoly in ht.
    apply Nat.le_trans with
      (coefficient p * (8 * (n + 1) ^ (k + 1 + (k + 1))) ^ degree p * (n + 1) ^ c).
    + apply Nat.mul_le_mono_r. apply Nat.le_trans with (1 := ht).
      apply Nat.mul_le_mono_l, Nat.pow_le_mono_l. exact hlen.
    + apply Nat.le_trans with (2 := hN n hn).
      rewrite Nat.pow_mul_l, <- Nat.pow_mul_r, (Nat.pow_add_r (n + 1)).
      apply Nat.eq_le_incl. ring.
  - rewrite hb, circuitSAT_encode. split; [intros [_ hs]; exact hs | intro hs; split; assumption].
Qed.
