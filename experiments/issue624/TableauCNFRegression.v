From Stdlib Require Import List Bool Arith Lia.
From proofs.complexity.rocq Require Import Complexity.
From proofs.experiments.issue532.rocq Require Import Machines.
From proofs.experiments.issue624.rocq Require Import
  CertificateCNF VerifierTableau SuccessorCNF InitialCNF RunCNF CookLevin.
Import ListNotations Complexity Machines CookLevin InitialCNF SuccessorCNF CertificateCNF.

Example full_tableau : forall np x,
  Satisfiable (tableauCNF np x) <-> np_language np x = true.
Proof. exact tableauCNF_iff. Qed.
Example rejecting_tableau : forall np x,
  (forall w, np_language np w = false) -> ~ Satisfiable (tableauCNF np x).
Proof. exact tableauCNF_rejecting_unsatisfiable. Qed.
Example overlong_tableau : forall np x cert a,
  evalPoly (np_certBound np) (length x) < length cert ->
  (forall v, v <= 2 * evalPoly (np_certBound np) (length x) ->
    a v = CertificateCNF.encodeCertificate cert v) ->
  evalCNF a (tableauCNF np x) = false.
Proof. exact tableauCNF_overlong_rejected. Qed.
Example wrong_successor_tableau : forall np x a c d rest,
  step (VerifierTableau.verifierMachine (np_verifier np)) c <> inr d ->
  decodeTrace np x a = c :: d :: rest -> evalCNF a (tableauCNF np x) = false.
Proof. exact tableauCNF_wrong_successor_rejected. Qed.
Example unary_encoded_size : forall np x,
  length (encodeCNF (tableauCNF np x)) <= evalPoly (sizePolynomial np) (length x).
Proof. exact tableauCNF_encoded_size. Qed.

(** A verifier rejects from state zero but accepts from state one. *)
Definition startSensitive (answer : bool) : Machine :=
  {| program := [[halt answer; halt answer; halt answer; halt answer];
    [halt true; halt true; halt true; halt true]] |}.
Definition startVerifier (isPaired answer : bool) : VerifierProgram :=
  if isPaired then paired (startSensitive answer) else ignoreCertificate (startSensitive answer).
Lemma startRun : forall isPaired answer x cert, verifierRun (startVerifier isPaired answer) x cert 1 answer.
Proof.
  intros [|] answer x cert; cbn [startVerifier verifierRun]; apply run_halt;
    destruct x as [|b rest]; [reflexivity|destruct b; reflexivity|reflexivity|destruct b; reflexivity].
Qed.
Lemma startTime : forall isPaired answer x cert,
  timeLimit (startVerifier isPaired answer) {| coefficient := 1; degree := 0 |} x cert = 1.
Proof. intros [|]; reflexivity. Qed.
Definition startNP (isPaired answer : bool) (bound : nat) : ClassNP.
Proof.
  refine {| np_language := fun _ => answer;
    np_verifier := startVerifier isPaired answer;
    np_certBound := {| coefficient := bound; degree := 0 |};
    np_timeBound := {| coefficient := 1; degree := 0 |} |}.
  - intros x cert _. exists 1, answer. split; [rewrite startTime; reflexivity|apply startRun].
  - intro x. split.
    + intro h. exists [], 1. split; [simpl; lia|]. split; [rewrite startTime; reflexivity|].
      rewrite <- h. apply startRun.
    + intros [cert [t [_ [_ hr]]]]. apply VerifierTableau.verifierRun_iff in hr.
      pose proof (startRun isPaired answer x cert) as hc. apply VerifierTableau.verifierRun_iff in hc.
      pose proof (run_deterministic _ _ _ _ _ _ hr hc) as [_ hb]. symmetry. exact hb.
Defined.
Definition wrongState : Config := {| state := 1; tapeLeft := [blank]; tapeHead := one;
  tapeRight := [separator; zero; blank; blank; blank; blank] |}.
Definition candidate (c : Config) : Assignment :=
  jointAssignment (startNP true false 2) [true] (encodeCertificate [false]) [c].
Example candidate_certificate : evalCNF (candidate wrongState) (certificateCNF 0 2) = true.
Proof. reflexivity. Qed.
Example unrelated_accepting_prefix :
  evalCNF (candidate wrongState) (RunCNF.runCNF (startSensitive false) 5 8 1) = true.
Proof. reflexivity. Qed.
Example wrong_initial_state_rejected : evalCNF (candidate wrongState) (tableauCNF (startNP true false 2) [true]) = false.
Proof. reflexivity. Qed.
Example rejecting_from_prescribed_start : forall isPaired x, ~ Satisfiable (tableauCNF (startNP isPaired false 2) x).
Proof. intros. apply tableauCNF_rejecting_unsatisfiable. reflexivity. Qed.
Definition wrongHead : Config := {| state := 0; tapeLeft := [one; blank]; tapeHead := separator;
  tapeRight := [zero; blank; blank; blank; blank] |}.
Definition wrongTape : Config := {| state := 0; tapeLeft := [blank]; tapeHead := one;
  tapeRight := [separator; one; blank; blank; blank; blank] |}.
Example wrong_head_valid_row : evalCNF (candidate wrongHead) (rowCNF 5 2 8) = true.
Proof. reflexivity. Qed.
Example wrong_tape_valid_row : evalCNF (candidate wrongTape) (rowCNF 5 2 8) = true.
Proof. reflexivity. Qed.
Example wrong_head_rejected :
  evalCNF (candidate wrongHead) (initialCNF 5 2 1 (sources (startNP true false 2) [true])) = false.
Proof. reflexivity. Qed.
Example wrong_tape_rejected :
  evalCNF (candidate wrongTape) (initialCNF 5 2 1 (sources (startNP true false 2) [true])) = false.
Proof. reflexivity. Qed.
Example paired_empty_sources : map (sourceEval (encodeCertificate []))
  (windowSources (paired (startSensitive true)) [] 2 1 6) = [blank; separator; blank; blank; blank; blank].
Proof. reflexivity. Qed.
Example paired_short_sources : map (sourceEval (encodeCertificate [false]))
  (windowSources (paired (startSensitive true)) [] 2 1 6) = [blank; separator; zero; blank; blank; blank].
Proof. reflexivity. Qed.
Example paired_full_sources : map (sourceEval (encodeCertificate [true; false]))
  (windowSources (paired (startSensitive true)) [] 2 1 6) = [blank; separator; one; zero; blank; blank].
Proof. reflexivity. Qed.
Example ignoring_sources : map (sourceEval (encodeCertificate [true; false]))
  (windowSources (ignoreCertificate (startSensitive true)) [] 2 1 6) = repeat blank 6.
Proof. reflexivity. Qed.
Definition acceptingModel (isPaired : bool) (x cert : Word) (bound : nat) : Assignment :=
  let np := startNP isPaired true bound in
  let a := encodeCertificate cert in jointAssignment np x a [initialRow np x a].
Example accepting_zero_bound :
  evalCNF (acceptingModel true [] [] 0) (tableauCNF (startNP true true 0) []) = true.
Proof. reflexivity. Qed.
Example accepting_empty :
  evalCNF (acceptingModel true [] [] 2) (tableauCNF (startNP true true 2) []) = true.
Proof. reflexivity. Qed.
Example accepting_short :
  evalCNF (acceptingModel true [] [false] 2) (tableauCNF (startNP true true 2) []) = true.
Proof. reflexivity. Qed.
Example accepting_full :
  evalCNF (acceptingModel true [] [true; false] 2) (tableauCNF (startNP true true 2) []) = true.
Proof. reflexivity. Qed.
Example accepting_ignoring :
  evalCNF (acceptingModel false [true] [true; false] 2) (tableauCNF (startNP false true 2) [true]) = true.
Proof. reflexivity. Qed.
Example decoded_short_certificate : decodeCertificate (acceptingModel true [] [false] 2) 0 2 = [false].
Proof. reflexivity. Qed.
Example decoded_short_trace : decodeTrace (startNP true true 2) [] (acceptingModel true [] [false] 2) =
  [initialRow (startNP true true 2) [] (encodeCertificate [false])].
Proof. reflexivity. Qed.

Print Assumptions tableauCNF_sound.
Print Assumptions tableauCNF_complete.
Print Assumptions tableauCNF_iff.
Print Assumptions tableauCNF_encoded_size.
Print Assumptions tableauCNF_rejecting_unsatisfiable.
Print Assumptions tableauCNF_overlong_rejected.
Print Assumptions tableauCNF_wrong_successor_rejected.
