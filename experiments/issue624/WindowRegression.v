From Stdlib Require Import List Bool Arith Lia.
From proofs.experiments.issue624.rocq Require Import FixedWindow.
Import ListNotations Complexity.Complexity Machines Tableau.Tableau.
Import CertificateCNF VerifierTableau FixedWindow.

Example window_language : forall np x,
  (exists a trace, WindowVerifierTableau np x a trace) <-> np_language np x = true.
Proof. apply windowVerifierTableau_iff_language. Qed.

Example fixed_width : forall c margin width,
  span c + 2 * margin <= width -> span (fitWindow c margin width) = width.
Proof. apply fitWindow_span. Qed.

Example empty_width : span (fitWindow (initial []) 2 7) = 7.
Proof. reflexivity. Qed.
Example empty_left : length (tapeLeft (fitWindow (initial []) 2 7)) = 2.
Proof. reflexivity. Qed.
Example empty_right : length (tapeRight (fitWindow (initial []) 2 7)) = 4.
Proof. reflexivity. Qed.

Example left_padding : forall c q w k,
  TapeEquivalent (moveHead c q w left)
    (moveHead (fitWindow c k (span c + 2 * k)) q w left).
Proof. intros. apply tapeEquivalent_moveHead. apply fitWindow_equivalent. Qed.

Example padding_run : forall m c t b k width,
  Run m (fitWindow c k width) t b <-> Run m c t b.
Proof. apply run_fitWindow_iff. Qed.

Example trace_states : forall m trace c,
  localTrace m true trace -> In c trace -> state c < length (program m).
Proof. intros. eapply accepting_trace_state_lt; eauto. Qed.

Example wrong_successor : ~ localTrace moveThenAccept true
  [fitWindow (initial []) 2 7; fitWindow wrongSuccessor 2 7].
Proof. cbv. intuition discriminate. Qed.

Print Assumptions windowVerifierTableau_iff_language.
Print Assumptions run_fitWindow_iff.
Print Assumptions trace_window_of_run.

Print Assumptions windowWidth_polynomial.
