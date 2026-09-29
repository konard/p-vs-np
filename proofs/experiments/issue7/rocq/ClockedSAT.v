(** * Issue 7: the clocked-SAT sentence over the shared model

    The Rocq twin of [proofs/experiments/issue7/lean/ClockedSAT.lean], with
    the same statement names.  It states the Σ⁰₂ form
    [exists m p, forall x, clockCheck m p x = true] of P = NP over the shared
    machine model, proves the clock lemma [runFor_iff] for a fuel-bounded
    interpreter of [Run], and relates the Σ⁰₂ and Π⁰₂ forms to [InP SAT],
    [PEqualsNP] and [PNotEqualsNP].  [SATHard] stays an explicit premise.  It
    also proves that the per-machine form "every clocked machine fails on some
    NP language" holds outright, so it cannot express P ≠ NP.  It does not
    prove P = NP, P ≠ NP, or anything about ZFC; the ZFC translation of the
    sentence is not formalized.  Nothing is assumed as an axiom. *)

From Stdlib Require Import Arith PeanoNat Lia Bool List Classical_Prop.
Import ListNotations.
From proofs.experiments.issue532.rocq Require Import Machines SATVerifier.

(** ** The clock lemma: a fuel-bounded interpreter for [Run] *)

(** Run [m] from [c] for at most [fuel] steps.  [Some (t, b)] means the
    machine halted with answer [b] after exactly [t] charged steps. *)
Fixpoint runFor (m : Machine) (c : Config) (fuel : nat) : option (nat * bool) :=
  match fuel with
  | 0 => None
  | S fuel' =>
    match step m c with
    | inl b => Some (1, b)
    | inr c' =>
      match runFor m c' fuel' with
      | Some (t, b) => Some (S t, b)
      | None => None
      end
    end
  end.

Theorem runFor_sound : forall m fuel c t b,
  runFor m c fuel = Some (t, b) -> Run m c t b /\ t <= fuel.
Proof.
  intros m fuel. induction fuel as [| fuel IH]; intros c t b h.
  - discriminate h.
  - simpl in h. destruct (step m c) as [b' | c'] eqn:hs.
    + inversion h; subst. split; [apply run_halt; exact hs | lia].
    + destruct (runFor m c' fuel) as [[t' b'] |] eqn:hr; [| discriminate h].
      inversion h; subst.
      destruct (IH c' t' b hr) as [hrun hle].
      split; [eapply run_next; eauto | lia].
Qed.

Theorem runFor_complete : forall m c t b,
  Run m c t b -> forall fuel, t <= fuel -> runFor m c fuel = Some (t, b).
Proof.
  intros m c t b h. induction h as [c b hs | c c' t b hs hr IH]; intros fuel hf.
  - destruct fuel as [| fuel]; [lia |]. simpl. rewrite hs. reflexivity.
  - destruct fuel as [| fuel]; [lia |]. simpl. rewrite hs.
    rewrite (IH fuel ltac:(lia)). reflexivity.
Qed.

(** The clock lemma: the interpreter returns exactly the runs that fit in the fuel. *)
Theorem runFor_iff : forall m c fuel t b,
  runFor m c fuel = Some (t, b) <-> Run m c t b /\ t <= fuel.
Proof.
  intros m c fuel t b. split.
  - apply runFor_sound.
  - intros [h hle]. exact (runFor_complete m c t b h fuel hle).
Qed.

(** ** The matrix R(e,k,x) *)

(** [R(e,k,x)]: [m] halts on [x] within the clock [p(|x|)] with the SAT answer. *)
Definition clockCheck (m : Machine) (p : Polynomial) (x : Word) : bool :=
  match runFor m (initial x) (evalPoly p (length x)) with
  | Some (_, b) => Bool.eqb b (SAT x)
  | None => false
  end.

(** The Prop-level matrix, as it occurs inside [DecidesWithin m p SAT]. *)
Definition ClockedCorrect (m : Machine) (p : Polynomial) (x : Word) : Prop :=
  exists t b, t <= evalPoly p (length x) /\ Run m (initial x) t b /\ b = SAT x.

(** The computable test decides the Prop-level matrix. *)
Theorem clockCheck_iff : forall m p x,
  clockCheck m p x = true <-> ClockedCorrect m p x.
Proof.
  intros m p x. unfold clockCheck. split.
  - destruct (runFor m (initial x) (evalPoly p (length x))) as [[t b] |] eqn:hr;
      [| discriminate].
    intro h. apply Bool.eqb_prop in h.
    destruct (runFor_sound _ _ _ _ _ hr) as [hrun hle].
    exists t, b. auto.
  - intros [t [b [hle [hrun hb]]]].
    rewrite (runFor_complete _ _ _ _ hrun _ hle). subst b. apply Bool.eqb_reflx.
Qed.

(** ** The Σ⁰₂ form and P = NP *)

(** The Σ⁰₂ form: one machine and one polynomial clock are correct on SAT for
    every input. *)
Definition ClockedSAT : Prop :=
  exists (m : Machine) (p : Polynomial), forall x, clockCheck m p x = true.

(** [ClockedSAT] is [PolyDec SAT], the machine-level SAT obligation. *)
Theorem clockedSAT_iff_polyDec : ClockedSAT <-> PolyDec SAT.
Proof.
  split.
  - intros [m [p h]]. exists m, p. intro x. exact (proj1 (clockCheck_iff m p x) (h x)).
  - intros [m [p h]]. exists m, p. intro x. exact (proj2 (clockCheck_iff m p x) (h x)).
Qed.

(** No hypothesis: the Σ⁰₂ form says exactly that SAT is in P. *)
Theorem clockedSAT_iff_inP_sat : ClockedSAT <-> InP SAT.
Proof. rewrite clockedSAT_iff_polyDec. apply polyDec_iff_inP. Qed.

(** No hypothesis: P = NP gives the Σ⁰₂ form, because [SATInNP] is proved. *)
Theorem clockedSAT_of_pEqualsNP : PEqualsNP -> ClockedSAT.
Proof. intro h. apply clockedSAT_iff_inP_sat. exact (inP_sat_of_pEqualsNP' h). Qed.

(** The converse needs the named hardness half of Cook-Levin. *)
Theorem pEqualsNP_of_clockedSAT : SATHard -> ClockedSAT -> PEqualsNP.
Proof.
  intros hard h. apply (pEqualsNP_of_inP_sat hard). exact (proj1 clockedSAT_iff_inP_sat h).
Qed.

(** With [SATHard], the Σ⁰₂ form is equivalent to P = NP. *)
Theorem clockedSAT_iff_pEqualsNP : SATHard -> (ClockedSAT <-> PEqualsNP).
Proof.
  intro hard. split; [exact (pEqualsNP_of_clockedSAT hard) | exact clockedSAT_of_pEqualsNP].
Qed.

(** ** The Π⁰₂ form and P ≠ NP *)

(** The Π⁰₂ form: the single language SAT defeats every machine and clock.
    The left-to-right direction uses excluded middle ([Classical_Prop.classic]). *)
Theorem not_clockedSAT_iff :
  ~ ClockedSAT <-> forall (m : Machine) (p : Polynomial), exists x, clockCheck m p x = false.
Proof.
  split.
  - intros h m p.
    destruct (classic (exists x, clockCheck m p x = false)) as [hx | hx]; [exact hx |].
    exfalso. apply h. exists m, p. intro x.
    destruct (clockCheck m p x) eqn:hc; [reflexivity |].
    exfalso. apply hx. exists x. exact hc.
  - intros h [m [p hall]]. destruct (h m p) as [x hx].
    rewrite hall in hx. discriminate hx.
Qed.

(** No hypothesis: the Π⁰₂ form gives P ≠ NP. *)
Theorem pNotEqualsNP_of_pi2 :
  (forall (m : Machine) (p : Polynomial), exists x, clockCheck m p x = false) -> PNotEqualsNP.
Proof.
  intros h hp. exact (proj2 not_clockedSAT_iff h (clockedSAT_of_pEqualsNP hp)).
Qed.

(** The converse needs [SATHard]. *)
Theorem pi2_of_pNotEqualsNP : SATHard -> PNotEqualsNP ->
  forall (m : Machine) (p : Polynomial), exists x, clockCheck m p x = false.
Proof.
  intros hard h. apply not_clockedSAT_iff. intro hc. exact (h (pEqualsNP_of_clockedSAT hard hc)).
Qed.

(** ** Quantifier order: the per-machine form is a theorem

    The corrected roadmap warns that "every polynomial-time machine fails to
    decide some NP language" is not P ≠ NP.  Here it is proved with no
    hypothesis: each machine and clock fails on one of the two constant
    languages, and both are in P. *)

(** The machine that halts with answer [b] in its first step. *)
Definition constMachine (b : bool) : Machine := {| program := [repeat (halt b) 4] |}.

Theorem step_constMachine : forall b c, state c = 0 -> step (constMachine b) c = inl b.
Proof.
  intros b [q l a r] h. simpl in h. subst q. destruct a; reflexivity.
Qed.

Theorem initial_state : forall x, state (initial x) = 0.
Proof. intros [| a x]; reflexivity. Qed.

Theorem inP_const : forall b : bool, InP (fun _ => b).
Proof.
  intro b. apply (inP_of_decidesWithin (constMachine b) {| coefficient := 1; degree := 0 |}).
  intro x. exists 1, b. split; [unfold evalPoly; simpl; lia |]. split; [| reflexivity].
  apply run_halt. apply step_constMachine. apply initial_state.
Qed.

(** For every machine and clock there is an NP language, even one in P, that
    the machine does not decide within the clock.  The language depends on
    the machine. *)
Theorem per_machine_form_holds : forall (m : Machine) (p : Polynomial),
  exists L : Language, InNP L /\ ~ DecidesWithin m p L.
Proof.
  intros m p.
  destruct (runFor m (initial []) (evalPoly p (length (@nil bool)))) as [[t0 b0] |] eqn:hr.
  - exists (fun _ => negb b0). split; [apply pSubsetNP, inP_const |].
    intro hd. destruct (hd []) as [t [b [hle [hrun hb]]]].
    rewrite (runFor_complete _ _ _ _ hrun _ hle) in hr.
    injection hr as ht hb0. subst t0 b0. destruct b; discriminate hb.
  - exists (fun _ => true). split; [apply pSubsetNP, inP_const |].
    intro hd. destruct (hd []) as [t [b [hle [hrun _]]]].
    rewrite (runFor_complete _ _ _ _ hrun _ hle) in hr. discriminate hr.
Qed.

(** ** Non-vacuity of [clockCheck] *)

(** The empty table rejects in its first step. *)
Definition rejectAll : Machine := {| program := [] |}.

(** [[[]]] has an empty clause, so the rejecting machine is right on it. *)
Theorem clockCheck_rejectAll_empty_clause :
  clockCheck rejectAll {| coefficient := 1; degree := 0 |} (encodeCNF [[]]) = true.
Proof. reflexivity. Qed.

(** The empty formula is satisfiable, so the rejecting machine is wrong on it. *)
Theorem clockCheck_rejectAll_empty_cnf : forall p : Polynomial,
  clockCheck rejectAll p (encodeCNF []) = false.
Proof.
  intro p. unfold clockCheck. destruct (evalPoly p (length (encodeCNF []))); reflexivity.
Qed.

(** A concrete Π⁰₂ instance: one machine is defeated for every clock. *)
Theorem rejectAll_defeated : forall p : Polynomial, exists x, clockCheck rejectAll p x = false.
Proof. intro p. exists (encodeCNF []). apply clockCheck_rejectAll_empty_cnf. Qed.

(** A zero clock admits no run, since every run charges at least one step. *)
Theorem clockCheck_zero_clock : forall m x,
  clockCheck m {| coefficient := 0; degree := 0 |} x = false.
Proof. intros m x. reflexivity. Qed.
