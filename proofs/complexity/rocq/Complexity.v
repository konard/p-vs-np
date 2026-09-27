(** A finite single-tape machine model shared by the Rocq P/NP statements.
    Each transition is selected from a finite program table. *)
From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.

Module Complexity.

Definition Word := list bool.
Definition Language := Word -> bool.

Inductive Symbol := blank | zero | one | separator.
Definition ofBool (b : bool) : Symbol := if b then one else zero.
Definition symbolIndex (a : Symbol) : nat :=
  match a with blank => 0 | zero => 1 | one => 2 | separator => 3 end.

Inductive Direction := left | right | stay.
Inductive Instruction := halt (answer : bool) |
  move (nextState : nat) (write : Symbol) (direction : Direction).

Record Machine := { program : list (list Instruction) }.
Record Config := {
  state : nat;
  tapeLeft : list Symbol;
  tapeHead : Symbol;
  tapeRight : list Symbol
}.

Definition initialSymbols (input : list Symbol) : Config :=
  match input with
  | [] => {| state := 0; tapeLeft := []; tapeHead := blank; tapeRight := [] |}
  | a :: rest => {| state := 0; tapeLeft := []; tapeHead := a; tapeRight := rest |}
  end.
Definition initial (input : Word) : Config :=
  initialSymbols (map ofBool input).
Definition pairedInput (input certificate : Word) : Config :=
  initialSymbols (map ofBool input ++ [separator] ++ map ofBool certificate).

Definition instruction (m : Machine) (q : nat) (a : Symbol) : Instruction :=
  match nth_error (program m) q with
  | None => halt false
  | Some row => match nth_error row (symbolIndex a) with
                | None => halt false | Some i => i end
  end.

Definition moveHead (c : Config) (next : nat) (write : Symbol)
    (direction : Direction) : Config :=
  match direction with
  | stay => {| state := next; tapeLeft := tapeLeft c;
               tapeHead := write; tapeRight := tapeRight c |}
  | left => match tapeLeft c with
    | [] => {| state := next; tapeLeft := []; tapeHead := blank;
               tapeRight := write :: tapeRight c |}
    | a :: rest => {| state := next; tapeLeft := rest; tapeHead := a;
                     tapeRight := write :: tapeRight c |}
    end
  | right => match tapeRight c with
    | [] => {| state := next; tapeLeft := write :: tapeLeft c;
               tapeHead := blank; tapeRight := [] |}
    | a :: rest => {| state := next; tapeLeft := write :: tapeLeft c;
                     tapeHead := a; tapeRight := rest |}
    end
  end.

(** Exactly one table instruction is charged per step. *)
Definition step (m : Machine) (c : Config) : bool + Config :=
  match instruction m (state c) (tapeHead c) with
  | halt b => inl b
  | move next write direction => inr (moveHead c next write direction)
  end.

Inductive Run (m : Machine) : Config -> nat -> bool -> Prop :=
| run_halt : forall c b, step m c = inl b -> Run m c 1 b
| run_next : forall c c' t b, step m c = inr c' ->
    Run m c' t b -> Run m c (S t) b.

Record Polynomial := {
  coefficient : nat;
  degree : nat
}.
Definition evalPoly (p : Polynomial) (n : nat) : nat :=
  coefficient p * (n + 1) ^ degree p.

Record ClassP := {
  p_language : Language;
  p_machine : Machine;
  p_bound : Polynomial;
  p_terminates : forall x, exists t b,
    t <= evalPoly p_bound (length x) /\ Run p_machine (initial x) t b;
  p_correct : forall x t b, Run p_machine (initial x) t b ->
    (p_language x = true <-> b = true)
}.

Inductive VerifierProgram :=
| ignoreCertificate (machine : Machine)
| paired (machine : Machine).

Definition verifierRun (v : VerifierProgram) (x cert : Word)
    (t : nat) (b : bool) : Prop :=
  match v with
  | ignoreCertificate m => Run m (initial x) t b
  | paired m => Run m (pairedInput x cert) t b
  end.

Definition timeLimit (v : VerifierProgram) (p : Polynomial)
    (x cert : Word) : nat :=
  match v with
  | ignoreCertificate _ => evalPoly p (length x)
  | paired _ => evalPoly p (length x + length cert + 1)
  end.

Record ClassNP := {
  np_language : Language;
  np_verifier : VerifierProgram;
  np_timeBound : Polynomial;
  np_certBound : Polynomial;
  np_terminates : forall x cert,
    length cert <= evalPoly np_certBound (length x) ->
    exists t b, t <= timeLimit np_verifier np_timeBound x cert /\
      verifierRun np_verifier x cert t b;
  np_correct : forall x, np_language x = true <->
    exists cert t, length cert <= evalPoly np_certBound (length x) /\
      t <= timeLimit np_verifier np_timeBound x cert /\
      verifierRun np_verifier x cert t true
}.

Definition InP (language : Language) : Prop :=
  exists p : ClassP, p_language p = language.
Definition InNP (language : Language) : Prop :=
  exists np : ClassNP, np_language np = language.
Definition PEqualsNP : Prop := forall language, InNP language -> InP language.
Definition PNotEqualsNP : Prop := ~ PEqualsNP.

Definition pToNP (p : ClassP) : ClassNP.
Proof.
  refine {| np_language := p_language p;
            np_verifier := ignoreCertificate (p_machine p);
            np_timeBound := p_bound p;
            np_certBound := {| coefficient := 0; degree := 0 |} |}.
  - intros x cert _.
    exact (p_terminates p x).
  - intro x. split.
    + intro hx.
      destruct (p_terminates p x) as [t [b [ht hr]]].
      assert (hb : b = true) by (apply (proj1 (p_correct p x t b hr)); exact hx).
      subst b.
      exists [], t. simpl. repeat split; auto; lia.
    + intros [cert [t [_ [_ hr]]]].
      apply (proj2 (p_correct p x t true hr)). reflexivity.
Defined.

Theorem pSubsetNP : forall language, InP language -> InNP language.
Proof.
  intros language [p hp].
  exists (pToNP p). exact hp.
Qed.

End Complexity.
