(** The six-state finite machine for the exact circuit encoding grammar.
    This checks syntax only, not wire bounds, length or NAND evaluation. *)
From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.
From proofs.experiments.issue532.rocq Require Import Idea41.
Import Complexity Machines Circuits.

Module CircuitSyntax.

Inductive Phase := header | marker | firstWire | secondWire | done | bad.

Definition next (q : Phase) (b : bool) : Phase :=
  match q, b with
  | header, true => header | header, false => marker
  | marker, true => firstWire | marker, false => done
  | firstWire, true => firstWire | firstWire, false => secondWire
  | secondWire, true => secondWire | secondWire, false => marker
  | done, _ => bad | bad, _ => bad
  end.

Definition finished (q : Phase) : bool := match q with done => true | _ => false end.

Fixpoint syntaxFrom (q : Phase) (w : Word) : bool :=
  match w with [] => finished q | b :: r => syntaxFrom (next q b) r end.

Definition circuitSyntax (w : Word) : bool := syntaxFrom header w.

Definition Suffix (q : Phase) (w : Word) : Prop :=
  match q with
  | header => exists n C, w = encCircuit n C
  | marker => exists C, w = encList encGate C
  | firstWire => exists i j C, w = encNat i ++ encNat j ++ encList encGate C
  | secondWire => exists j C, w = encNat j ++ encList encGate C
  | done => w = []
  | bad => False
  end.

Theorem syntaxFrom_sound : forall q w, syntaxFrom q w = true -> Suffix q w.
Proof.
  intros q w. revert q. induction w as [| b w IH]; intros q h.
  - destruct q; simpl in *; try discriminate. reflexivity.
  - change (syntaxFrom (next q b) w = true) in h.
    specialize (IH (next q b) h).
    destruct q, b; cbn [next Suffix] in IH |- *; try contradiction.
    + destruct IH as [n [C ->]]. exists (S n), C. reflexivity.
    + destruct IH as [C ->]. exists 0, C. reflexivity.
    + destruct IH as [i [j [C ->]]]. exists ((i, j) :: C).
      cbn [encList]. unfold encGate. cbn [fst snd]. now rewrite <- app_assoc.
    + subst w. exists []. reflexivity.
    + destruct IH as [i [j [C ->]]]. exists (S i), j, C. reflexivity.
    + destruct IH as [j [C ->]]. exists 0, j, C. reflexivity.
    + destruct IH as [j [C ->]]. exists (S j), C. reflexivity.
    + destruct IH as [C ->]. exists 0, C. reflexivity.
Qed.

Theorem syntaxFrom_nat : forall q, next q true = q -> forall n r,
  syntaxFrom q (encNat n ++ r) = syntaxFrom (next q false) r.
Proof.
  intros q hq n. induction n as [| n IH]; intro r; simpl; [reflexivity |].
  rewrite hq. apply IH.
Qed.

Theorem syntaxFrom_list : forall C, syntaxFrom marker (encList encGate C) = true.
Proof.
  induction C as [| [i j] C IH]; [reflexivity |].
  cbn [encList syntaxFrom next]. unfold encGate. cbn [fst snd].
  rewrite <- app_assoc, (syntaxFrom_nat firstWire eq_refl).
  cbn [next]. rewrite (syntaxFrom_nat secondWire eq_refl). exact IH.
Qed.

Theorem circuitSyntax_encCircuit : forall n C, circuitSyntax (encCircuit n C) = true.
Proof.
  intros n C. unfold circuitSyntax, encCircuit.
  rewrite (syntaxFrom_nat header eq_refl). apply syntaxFrom_list.
Qed.

Theorem circuitSyntax_iff : forall w,
  circuitSyntax w = true <-> exists n C, w = encCircuit n C.
Proof.
  intro w. split; [apply syntaxFrom_sound |].
  intros [n [C ->]]. apply circuitSyntax_encCircuit.
Qed.

Theorem circuitSyntax_iff_decCircuit : forall w,
  circuitSyntax w = true <-> exists n C, decCircuit w = Some (n, C).
Proof.
  intro w. rewrite circuitSyntax_iff. split.
  - intros [n [C ->]]. exists n, C. apply decCircuit_encCircuit.
  - intros [n [C hd]]. exists n, C. apply decCircuit_sound. exact hd.
Qed.

Definition idx (q : Phase) : nat :=
  match q with header => 0 | marker => 1 | firstWire => 2 |
    secondWire => 3 | done => 4 | bad => 5 end.

Definition phases := [header; marker; firstWire; secondWire; done; bad].

Definition delta (q : Phase) (a : Symbol) : Instruction :=
  match a with
  | zero => move (idx (next q false)) zero right
  | one => move (idx (next q true)) one right
  | separator => halt (finished q)
  | blank => halt false
  end.

Definition row (q : Phase) := [delta q blank; delta q zero; delta q one; delta q separator].
Definition circuitSyntaxMachine : Machine := {| program := map row phases |}.

Theorem instruction_spec : forall q a, instruction circuitSyntaxMachine (idx q) a = delta q a.
Proof. destruct q, a; reflexivity. Qed.

Definition cfg (q : Phase) (L R : list Symbol) : Config :=
  match R with
  | [] => {| state := idx q; tapeLeft := L; tapeHead := blank; tapeRight := [] |}
  | a :: R' => {| state := idx q; tapeLeft := L; tapeHead := a; tapeRight := R' |}
  end.

Theorem scan_run : forall q w L R,
  Run circuitSyntaxMachine (cfg q L (map ofBool w ++ separator :: R))
    (length w + 1) (syntaxFrom q w).
Proof.
  intros q w. revert q. induction w as [| b w IH]; intros q L R.
  - apply run_halt. destruct q; reflexivity.
  - change (Run circuitSyntaxMachine (cfg q L (ofBool b :: (map ofBool w ++ separator :: R)))
      (S (length w + 1)) (syntaxFrom (next q b) w)).
    eapply run_next with (c' := cfg (next q b) (ofBool b :: L)
      (map ofBool w ++ separator :: R)); [| apply IH].
    destruct q, b, w; reflexivity.
Qed.

Theorem circuitSyntaxMachine_run : forall x cert,
  Run circuitSyntaxMachine (pairedInput x cert) (length x + 1) (circuitSyntax x).
Proof.
  intros x cert. change (Run circuitSyntaxMachine
    (cfg header [] (map ofBool x ++ separator :: map ofBool cert))
    (length x + 1) (syntaxFrom header x)).
  apply scan_run.
Qed.

Definition syntaxTimeBound : Polynomial := {| coefficient := 1; degree := 1 |}.

Theorem circuitSyntaxMachine_terminates : forall x cert,
  exists t b, t <= timeLimit (paired circuitSyntaxMachine) syntaxTimeBound x cert /\
    Run circuitSyntaxMachine (pairedInput x cert) t b.
Proof.
  intros x cert. exists (length x + 1), (circuitSyntax x). split.
  - unfold timeLimit, syntaxTimeBound, evalPoly. simpl. lia.
  - apply circuitSyntaxMachine_run.
Qed.

Theorem circuitSyntaxMachine_correct : forall x cert t b,
  Run circuitSyntaxMachine (pairedInput x cert) t b ->
    t = length x + 1 /\ b = circuitSyntax x.
Proof.
  intros x cert t b hr. exact (run_deterministic _ _ _ _ _ _ hr (circuitSyntaxMachine_run x cert)).
Qed.

Theorem circuitSyntaxMachine_accepts_iff : forall x cert,
  (exists t, Run circuitSyntaxMachine (pairedInput x cert) t true) <->
    exists n C, x = encCircuit n C.
Proof.
  intros x cert. rewrite <- circuitSyntax_iff. split.
  - intros [t hr]. symmetry. apply (circuitSyntaxMachine_correct _ _ _ _ hr).
  - intro hx. exists (length x + 1). rewrite <- hx. apply circuitSyntaxMachine_run.
Qed.

End CircuitSyntax.
