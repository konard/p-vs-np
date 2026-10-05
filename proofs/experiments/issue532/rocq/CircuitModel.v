From Stdlib Require Import Arith PeanoNat Lia Bool List.
Import ListNotations.
From proofs.complexity.rocq Require Export Complexity.
Export Complexity.Complexity.

(** Shared NAND definitions, independent of the machine compiler. *)
(** Gate [(i, j)] appends the NAND of wires [i] and [j]. *)
Definition Circuit := list (nat * nat).

Definition wire (w : list bool) (i : nat) : bool := nth i w false.

(** All wire values: the inputs followed by one wire per gate. *)
Fixpoint wires (w : list bool) (C : Circuit) : list bool :=
  match C with
  | [] => w
  | (i, j) :: C' => wires (w ++ [negb (wire w i && wire w j)]) C'
  end.

(** The output is the last wire ([false] if there are no wires). *)
Definition output (x : Word) (C : Circuit) : bool := last (wires x C) false.

(** Gate [k] only reads the [N] earlier wires. *)
Fixpoint WFfrom (N : nat) (C : Circuit) : Prop :=
  match C with
  | [] => True
  | (i, j) :: C' => i < N /\ j < N /\ WFfrom (N + 1) C'
  end.

(** A well-formed circuit on [n] inputs. *)
Definition WF (n : nat) (C : Circuit) : Prop := WFfrom n C.

(** [C] is a well-formed circuit on [n] inputs that agrees with [L] on every
    word of length [n]. *)
Definition CircuitDecides (n : nat) (C : Circuit) (L : Language) : Prop :=
  WF n C /\ forall x : Word, length x = n -> output x C = L x.

(** The class P/poly: [L] has circuits with polynomially many gates at every
    positive input length.

    Length [0] is excluded on purpose.  A well-formed circuit on [0] inputs
    has no gates ([WF 0 C] forces [C = []]), so its output is the constant
    [false].  If length [0] counted, every language with [L [] = true] (SAT
    among them, since the empty CNF is satisfiable) would be outside P/poly
    for a trivial reason, and [PSubsetPPoly] would be false.  One word per
    length changes no asymptotic notion. *)
Definition InPPoly (L : Language) : Prop :=
  exists p : Polynomial, forall n, 0 < n ->
    exists C : Circuit, length C <= evalPoly p n /\ CircuitDecides n C L.

Definition PSubsetPPoly : Prop := forall L : Language, InP L -> InPPoly L.

Theorem wire_append_self : forall (x : list bool) (b : bool),
  wire (x ++ [b]) (length x) = b.
Proof. intros x b. unfold wire. apply nth_middle. Qed.

Theorem wire_append_lt : forall (x : list bool) (b : bool) (i : nat),
  i < length x -> wire (x ++ [b]) i = wire x i.
Proof. intros x b i h. unfold wire. apply app_nth1. exact h. Qed.

