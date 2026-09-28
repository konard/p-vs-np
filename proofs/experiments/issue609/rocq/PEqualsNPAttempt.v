(** A conditional P = NP route over the shared finite-table machine and SAT.
    The matching Lean file has the same statements. No SAT machine is assumed
    to exist. [SATHard] remains an explicit premise. *)

From Stdlib Require Import Bool List.
Import ListNotations.
From proofs.experiments.issue532.rocq Require Import Machines.
From proofs.experiments.issue532.rocq Require Import SATVerifier.

Record Candidate := {
  machine : Machine;
  bound : Polynomial;
  terminates : forall x : Word, exists t b,
    t <= evalPoly bound (length x) /\ Run machine (initial x) t b;
  correct : forall x t b, Run machine (initial x) t b -> b = SAT x
}.

Theorem candidate_decides (c : Candidate) : DecidesWithin (machine c) (bound c) SAT.
Proof.
  intro x. destruct (terminates c x) as [t [b [ht hr]]].
  exists t, b. repeat split; auto. apply (correct c x t b hr).
Qed.

Theorem pEqualsNP_of_candidate (hard : SATHard) (c : Candidate) : PEqualsNP.
Proof. apply (pEqualsNP_of_inP_sat hard).
       exact (inP_of_decidesWithin (machine c) (bound c) SAT (candidate_decides c)). Qed.

Theorem candidate_of_inP (h : InP SAT) : exists c : Candidate, True.
Proof.
  apply polyDec_iff_inP in h. destruct h as [m [p hm]].
  refine (ex_intro _ {| machine := m; bound := p;
                        terminates := _; correct := _ |} I).
  - intro x. destruct (hm x) as [t [b [ht [hr hb]]]].
    exists t, b. split; assumption.
  - intros x t b hr. destruct (hm x) as [t' [b' [ht' [hr' hb']]]].
    destruct (run_deterministic m (initial x) t t' b b' hr hr') as [_ hbb'].
    rewrite hbb'. exact hb'.
Qed.

Theorem candidate_iff_pEqualsNP (hard : SATHard) :
  (exists c : Candidate, True) <-> PEqualsNP.
Proof.
  split.
  - intros [c _]. exact (pEqualsNP_of_candidate hard c).
  - intro h. apply candidate_of_inP.
    exact (inP_sat_of_pEqualsNP SATVerifier.satInNP h).
Qed.

Theorem candidate_on_encodings (c : Candidate) (phi : CNF) :
  exists t b, t <= evalPoly (bound c) (length (encodeCNF phi)) /\
    Run (machine c) (initial (encodeCNF phi)) t b /\
    (b = true <-> Satisfiable phi).
Proof.
  destruct (terminates c (encodeCNF phi)) as [t [b [ht hr]]].
  exists t, b. split; [exact ht|]. split; [exact hr|].
  rewrite (correct c (encodeCNF phi) t b hr). apply sat_encode.
Qed.

Theorem sat_has_yes_instance : SAT (encodeCNF ([] : CNF)) = true.
Proof. reflexivity. Qed.

Theorem sat_has_no_instance : SAT (encodeCNF ([[]] : CNF)) = false.
Proof. reflexivity. Qed.

Theorem not_every_language_inP : ~ (forall L : Language, InP L).
Proof. intro h. exact (diag_not_inP (h Diag)). Qed.
